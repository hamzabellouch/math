import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.TypeIIDefinitions

namespace OAI

/-! Projection comparison and matrix structure in finite type-II algebras. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace HochschildTypeII
open BoundedHochschild HochschildRigidity HochschildDiffuse HochschildComparison
open FinitePathMain
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma central_annihilator_chain (p : M) (c : Set M) (hc : IsChain (· ≤ ·) c)
    (hne : c.Nonempty) (hs : ∀ q ∈ c, CentralProjection q ∧ q*p=0) :
    ∃ s : M, CentralProjection s ∧ s*p=0 ∧ ∀ q ∈ c, q ≤ s := by
  classical
  let T : Set ℝ := (fun q : M => (τ q).re) '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := ⟨(τ 1).re,by
    rintro _ ⟨q,hq,rfl⟩
    exact Complex.re_le_re (τ.monotone (hs q hq).1.1.le_one)⟩
  obtain ⟨v,hvm,_hvL,hvt,hv⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hav using hv
  change ∀ n, (τ (a n)).re=v n at hav
  have ham : Monotone a := by
    intro m n hmn
    apply projection_le_of_comparable_trace_le τ hfaith (hs _ (ha m)).1.1 (hs _ (ha n)).1.1
      (hc.total (ha m) (ha n))
    rw [hav,hav]
    exact hvm hmn
  let L := HochschildSakai.mul_hasPreadjoint e
  obtain ⟨s,hsp,ht,hns,hsl⟩ := exists_monotone_projection_limit e τ L hτ htr hfaith
    a (fun n => (hs _ (ha n)).1.1) ham
  have htrace : (τ s).re=sSup T := by
    have htd := trace_predual_tendsto e τ hτ
      (predual_tendsto_of_preGNS e τ L hτ hfaith 1
        (fun n => (hs _ (ha n)).1.1.norm_le _) ht)
    apply tendsto_nhds_unique (Complex.continuous_re.tendsto _ |>.comp htd)
    simpa only [Function.comp_def,hav] using hvt
  refine ⟨s,⟨hsp,?_⟩,?_,?_⟩
  · intro b
    apply GNSTendsto.unique τ hfaith
      (ht.mul τ htr (GNSTendsto.const τ b atTop) 1 (fun n => (hs _ (ha n)).1.1.norm_le _))
    have hh := (GNSTendsto.const τ b atTop).mul τ htr ht ‖b‖ (fun _ => le_rfl)
    simpa only [(hs _ (ha _)).1.2 b |>.eq] using hh
  · apply GNSTendsto.unique τ hfaith
      (ht.mul τ htr (GNSTendsto.const τ p atTop) 1 (fun n => (hs _ (ha n)).1.1.norm_le _))
    simpa only [(hs _ (ha _)).2] using GNSTendsto.const τ (0:M) atTop
  · intro q hq
    by_cases hex : ∃ n, q ≤ a n
    · obtain ⟨n,hn⟩ := hex
      exact hn.trans (hns n)
    · have hanq : ∀ n, a n ≤ q := fun n =>
        (hc.total (ha n) hq).resolve_right (fun h => hex ⟨n,h⟩)
      apply projection_le_of_comparable_trace_le τ hfaith (hs q hq).1.1 hsp
        (Or.inr (hsl q (hs q hq).1.1 hanq))
      rw [htrace]
      exact le_csSup hTbd ⟨q,hq,rfl⟩

lemma abelian_of_le {p q : M} (hp : AbelianProjection p)
    (hq : IsStarProjection q) (hqp : q ≤ p) : AbelianProjection q := by
  refine ⟨hq,?_⟩
  intro a b
  have he (x : M) : p*(q*x*q)*p=q*x*q := by
    rw [← mul_assoc,← mul_assoc,(hq.le_iff_mul_eq_right hp.1).mp hqp,
      mul_assoc,mul_assoc,(hq.le_iff_mul_eq_left hp.1).mp hqp,← mul_assoc]
  simpa only [he] using hp.2 (q*a*q) (q*b*q)

lemma projection_orthogonal_of_le_complement {s c : M}
    (hs : IsStarProjection s) (hc : IsStarProjection c) (hcs : c ≤ 1-s) : s*c=0 := by
  have h := (hc.le_iff_mul_eq_right hs.one_sub).mp hcs
  rw [sub_mul,one_mul] at h
  exact sub_eq_self.mp h

include e hτ htr hfaith in

theorem exists_typeI_support {p : M} (hp : AbelianProjection p) (hp0 : p ≠ 0) :
    ∃ z : M, TypeICentralSummand z ∧ p ≤ z ∧ z ≠ 0 := by
  classical
  let S : Set M := {s | CentralProjection s ∧ s*p=0}
  have hz : (0:M) ∈ S := ⟨⟨IsStarProjection.zero M,fun _ => Commute.zero_left _⟩,zero_mul _⟩
  obtain ⟨s,_hs0,hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨t,ht,htp,hupper⟩ := central_annihilator_chain e τ hτ htr hfaith
      p c hchain ⟨y,hy⟩ (fun q hq => hc hq)
    exact ⟨t,⟨ht,htp⟩,hupper⟩) 0 hz
  have hs : CentralProjection s := hmax.1.1
  have hsp : s*p=0 := hmax.1.2
  have hzc : CentralProjection (1-s) :=
    ⟨hs.1.one_sub,fun a => (Commute.one_left a).sub_left (hs.2 a)⟩
  have hpz : p ≤ 1-s := (hp.1.le_iff_mul_eq_right hs.1.one_sub).mpr
    (by rw [sub_mul,one_mul,hsp,sub_zero])
  refine ⟨1-s,⟨hzc,?_⟩,hpz,?_⟩
  · intro c hc hcz hc0
    have hcp : IsStarProjection (c*p) := hc.1.mul hp.1 (hc.2 p)
    have hcpp : c*p ≤ p := (hcp.le_iff_mul_eq_left hp.1).mpr
      (by rw [mul_assoc,hp.1.isIdempotentElem.eq])
    have hcpc : c*p ≤ c := (hcp.le_iff_mul_eq_right hc.1).mpr
      (by rw [← mul_assoc,hc.1.isIdempotentElem.eq])
    refine ⟨c*p,abelian_of_le hp hcp hcpp,hcpc,?_⟩
    intro hzero
    have hsc := projection_orthogonal_of_le_complement hs.1 hc.1 hcz
    have hnew : s+c ∈ S := ⟨⟨hs.1.add hc.1 hsc,
      fun a => (hs.2 a).add_left (hc.2 a)⟩,by rw [add_mul,hsp,hzero,zero_add]⟩
    have hle : s ≤ s+c := le_add_of_nonneg_right hc.1.nonneg
    have he := le_antisymm (hmax.2 hnew hle) hle
    exact hc0 (add_eq_left.mp he)
  · intro he
    exact hp0 (le_antisymm (he ▸ hpz) hp.1.nonneg)

include e hτ htr hfaith in
theorem no_abelian_projection (hII : TypeII1 M) {p : M}
    (hp : AbelianProjection p) : p=0 := by
  by_contra hp0
  obtain ⟨z,hz,_hpz,hz0⟩ := exists_typeI_support e τ hτ htr hfaith hp hp0
  exact hz0 (hII.2 z hz)

lemma projection_orthogonal_of_le_sub {p q r : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hr : IsStarProjection r)
    (hqp : q ≤ p) (hrpq : r ≤ p-q) : q*r=0 := by
  have hpr := (hq.le_iff_sub hp).mp hqp
  have hh := (hr.le_iff_mul_eq_right hpr).mp hrpq
  calc
    q*r = q*((p-q)*r) := by rw [hh]
    _ = (q*p-q*q)*r := by noncomm_ring
    _ = 0 := by rw [(hq.le_iff_mul_eq_left hp).mp hqp,hq.isIdempotentElem.eq,sub_self,zero_mul]

include e hτ htr hfaith in

theorem exists_orthogonal_equivalent (hII : TypeII1 M) {p : M}
    (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ v : PartialIso M, (v:M) ≠ 0 ∧ v.initial ≤ p ∧ v.final ≤ p ∧
      v.initial*v.final=0 := by
  classical
  by_contra hn
  have hoff : ∀ q : M, IsStarProjection q → q ≤ p → ∀ b : M, q*b*(p-q)=0 := by
    intro q hq hqp b
    by_contra hb
    have hpr := (hq.le_iff_sub hp).mp hqp
    obtain ⟨v,hv0,hvi,hvf⟩ := partialIso_of_nonzero_corner e hq hpr
      (q*b*(p-q)) hb
      (by rw [← mul_assoc,← mul_assoc,hq.isIdempotentElem.eq])
      (by rw [mul_assoc,hpr.isIdempotentElem.eq])
    have hqi := projection_orthogonal_of_le_sub hp hq v.initial_proj hqp hvi
    have hfi : v.final*v.initial=0 := by
      calc
        v.final*v.initial = (v.final*q)*v.initial := by
          rw [(v.final_proj.le_iff_mul_eq_left hq).mp hvf]
        _ = 0 := by rw [mul_assoc,hqi,mul_zero]
    have hif : v.initial*v.final=0 := by
      simpa only [star_mul,v.initial_proj.isSelfAdjoint.star_eq,
        v.final_proj.isSelfAdjoint.star_eq,star_zero] using congrArg star hfi
    exact hn ⟨v,hv0,hvi.trans (sub_le_self _ hq.nonneg),hvf.trans hqp,hif⟩
  have hcomm (q : M) (hq : IsStarProjection q) (hqp : q ≤ p)
      (b : M) (hb : b ∈ HochschildCorners.corner p hp) : Commute q b := by
    have h1 := hoff q hq hqp b
    rw [mul_sub,mul_assoc,hb.2] at h1
    have hr := (hq.le_iff_sub hp).mp hqp
    have h2 := hoff (p-q) hr (sub_le_self _ hq.nonneg) b
    have he : p-(p-q)=q := by abel
    rw [he,sub_mul,sub_mul,hb.1] at h2
    change q*b=b*q
    exact (sub_eq_zero.mp h1).trans (sub_eq_zero.mp h2).symm
  have hab : AbelianProjection p := by
    refine ⟨hp,fun a b => ?_⟩
    apply HochschildCorners.commute_corner_of_projections e hp
      (fun q hq hqp => hcomm q hq hqp (p*b*p) (HochschildCorners.compress_mem_corner hp b))
      (HochschildCorners.compress_mem_corner hp a)
  exact hp0 (no_abelian_projection e τ hτ htr hfaith hII hab)

end HochschildTypeII

end

end OAI
