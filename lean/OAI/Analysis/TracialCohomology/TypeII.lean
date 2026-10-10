import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.Corners

namespace OAI

/-! Type ii for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def NoAbelianCorners (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] : Prop :=
  ∀ (p : M) (hp : IsStarProjection p), p ≠ 0 →
    ∃ a b : PopaCorner.algebra hp, ¬ Commute a b

lemma projection_commute_of_all (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M)
    (ha : ∀ q : M, IsStarProjection q → Commute q a) (b : M) : Commute b a := by
  let T : M →L[ℂ] M := (ContinuousLinearMap.mul ℂ M).flip a-(ContinuousLinearMap.mul ℂ M) a
  have hs : Submodule.span ℂ {q : M | IsStarProjection q} ≤ T.ker := by
    apply Submodule.span_le.mpr
    intro q hq
    change q*a-a*q=0
    exact sub_eq_zero.mpr (ha q hq).eq
  have hc : (Submodule.span ℂ {q : M | IsStarProjection q}).topologicalClosure ≤ T.ker :=
    Submodule.topologicalClosure_minimal _ hs T.isClosed_ker
  rw [HochschildSakai.projection_span_dense e] at hc
  exact sub_eq_zero.mp (hc (Submodule.mem_top : b ∈ (⊤ : Submodule ℂ M)))

omit [PartialOrder M] [StarOrderedRing M] in
lemma off_diagonal_nonzero {q a : M} (hq : IsStarProjection q) (hqa : ¬ Commute q a) :
    (1-q)*a*q ≠ 0 ∨ (1-q)*star a*q ≠ 0 := by
  by_contra h
  push Not at h
  have hstar := congrArg star h.2
  simp only [star_mul,star_sub,star_one,star_star,hq.isSelfAdjoint.star_eq,star_zero] at hstar
  have hright : a*q=q*a*q := by
    have hh := h.1
    rw [sub_mul,one_mul,sub_mul,sub_eq_zero] at hh
    exact hh
  have hleft : q*a=q*a*q := by
    simpa only [mul_sub,mul_one,sub_eq_zero,mul_assoc] using hstar
  exact hqa (show q*a=a*q from hleft.trans hright.symm)

theorem orthogonal_pair (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hII : NoAbelianCorners M) {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ v : PopaCorners.CornerIso p p, v.initial*v.final=0 ∧ (v:M) ≠ 0 := by
  classical
  let N := PopaCorner.algebra hp
  let eN := PopaCorner.predualEquiv e hp
  obtain ⟨a,b,hab⟩ := hII p hp hp0
  have hex : ∃ q : N, IsStarProjection q ∧ ¬ Commute q b := by
    by_contra hh
    push Not at hh
    exact hab (projection_commute_of_all eN b hh a)
  obtain ⟨q,hq,hqb⟩ := hex
  obtain ⟨y,hy⟩ : ∃ y : N, (1-q)*y*q ≠ 0 := by
    rcases off_diagonal_nonzero hq hqb with h | h
    · exact ⟨b,h⟩
    · exact ⟨star b,h⟩
  have h1q := hq.one_sub
  have hr := (hq.map (PopaCorner.incl hp))
  have hs := (h1q.map (PopaCorner.incl hp))
  let Q : M := (q:N)
  let R : M := ((1-q:N):N)
  let B : M := (((1-q)*y*q:N):N)
  have hB0 : B ≠ 0 := fun hh => hy (Subtype.ext hh)
  have hBQ : B*Q=B := by
    change (((1-q)*y*q:N):M)*(q:M)=_
    exact congrArg Subtype.val (show ((1-q)*y*q)*q=(1-q)*y*q from by rw [mul_assoc,hq.isIdempotentElem.eq])
  have hRB : R*B=B := by
    exact congrArg Subtype.val (show (1-q)*((1-q)*y*q)=(1-q)*y*q from by
      rw [←mul_assoc,←mul_assoc,h1q.isIdempotentElem.eq])
  obtain ⟨v,r,s,hr',hs',hrQ,hsR,hvi,hvf,hvr,hsv,hB⟩ := PopaCorners.corner_polar e hr hs hBQ hRB
  have hQp : Q ≤ p := (hr.le_iff_mul_eq_right hp).mpr q.property.1
  have hRp : R ≤ p := (hs.le_iff_mul_eq_right hp).mpr (1-q:N).property.1
  let V : PopaCorners.CornerIso p p := ⟨v,by rwa [hvi],by rwa [hvi],by rw [hvi]; exact hrQ.trans hQp,by rw [hvf]; exact hsR.trans hRp⟩
  have hQR : Q*R=0 := congrArg Subtype.val (show q*(1-q)=0 from by
    rw [mul_sub,mul_one,hq.isIdempotentElem.eq,sub_self])
  have hrs : r*s=0 := by
    have hrQ' : r*Q=r := (hr'.le_iff_mul_eq_left hr).mp hrQ
    have hRs : R*s=s := (hs'.le_iff_mul_eq_right hs).mp hsR
    calc
      r*s=(r*Q)*(R*s) := by rw [hrQ',hRs]
      _=0 := by simp only [mul_assoc,←mul_assoc Q R s,hQR,zero_mul,mul_zero]
  refine ⟨V,?_,?_⟩
  · change (star v*v)*(v*star v)=0
    rwa [hvi,hvf]
  · intro hv
    change v=0 at hv
    exact hB0 (by simpa only [hv,zero_mul] using hB)

end PopaTypeII

open Filter Topology
open scoped ComplexOrder
namespace PopaTypeII
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [StarOrderedRing M] in
lemma square_zero_iff {p : M} (v : CornerIso p p) :
    (v:M)*(v:M)=0 ↔ v.initial*v.final=0 := by
  constructor
  · intro h
    change (star (v:M)*(v:M))*((v:M)*star (v:M))=0
    calc
      _=star (v:M)*((v:M)*(v:M))*star (v:M) := by simp only [mul_assoc]
      _=0 := by rw [h,mul_zero,zero_mul]
  · intro h
    calc
      _=((v:M)*v.initial)*(v.final*(v:M)) := by rw [v.mul_initial,v.final_mul]
      _=(v:M)*(v.initial*v.final)*(v:M) := by simp only [mul_assoc]
      _=0 := by rw [h,mul_zero,zero_mul]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma square_zero_chain_upper {p : M} (hp : IsStarProjection p)
    (c : Set (CornerIso p p)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hz : ∀ v ∈ c, (v:M)*(v:M)=0) :
    ∃ w : CornerIso p p, (w:M)*(w:M)=0 ∧ ∀ v ∈ c, v ≤ w := by
  classical
  let T : Set ℝ := rank τ '' c
  have hTne : T.Nonempty := Set.Nonempty.image _ hne
  have hTbd : BddAbove T := by
    refine ⟨(τ p).re,?_⟩
    rintro _ ⟨v,hv,rfl⟩
    exact Complex.re_le_re (τ.monotone v.init_le)
  obtain ⟨t,htm,_htL,htt,htc⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
  choose a ha hat using htc
  change ∀ n, rank τ (a n)=t n at hat
  have ham : Monotone a := by
    intro m n hmn
    apply le_of_comparable_rank_le τ hfaith (hc.total (ha m) (ha n))
    rw [hat,hat]
    exact htm hmn
  obtain ⟨w,hwt,hwn,hwl⟩ := monotone_limit e τ hτ htr hfaith hp hp a ham
  have hwz : (w:M)*(w:M)=0 := GNSTendsto.unique τ hfaith
    (hwt.mul τ htr hwt 1 (fun n => (a n).norm_le_one))
    (by simpa only [hz _ (ha _)] using GNSTendsto.const τ (0:M) atTop)
  have hwr : rank τ w=sSup T := by
    apply tendsto_nhds_unique (rank_tendsto e τ hτ htr hfaith hwt)
    simpa only [hat] using htt
  refine ⟨w,hwz,?_⟩
  intro v hv
  by_cases hex : ∃ n, v ≤ a n
  · obtain ⟨n,hn⟩ := hex
    exact hn.trans (hwn n)
  · have haw : ∀ n, a n ≤ v := by
      intro n
      exact (hc.total (ha n) hv).resolve_right (fun h => hex ⟨n,h⟩)
    apply le_of_comparable_rank_le τ hfaith (Or.inr (hwl v haw))
    rw [hwr]
    exact le_csSup hTbd ⟨v,hv,rfl⟩

include e hτ htr hfaith in
lemma maximal_square_zero {p : M} (hp : IsStarProjection p) :
    ∃ v : CornerIso p p, (v:M)*(v:M)=0 ∧
      ∀ w : CornerIso p p, (w:M)*(w:M)=0 → v ≤ w → w ≤ v := by
  classical
  let S : Set (CornerIso p p) := {v | (v:M)*(v:M)=0}
  have hz : zero hp hp ∈ S := by change (0:M)*0=0; simp
  obtain ⟨v,hv,hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨w,hwz,hw⟩ := square_zero_chain_upper e τ hτ htr hfaith hp c hchain ⟨y,hy⟩
      (fun v hv => hc hv)
    exact ⟨w,hwz,hw⟩) (zero hp hp) hz
  exact ⟨v,hmax.1,fun w hw hle => hmax.2 hw hle⟩

include e hτ htr hfaith in

theorem halve_projection (hII : NoAbelianCorners M) {p : M} (hp : IsStarProjection p) :
    ∃ v : CornerIso p p, v.initial*v.final=0 ∧ v.initial+v.final=p := by
  obtain ⟨v,hvz,hmax⟩ := maximal_square_zero e τ hτ htr hfaith hp
  have hvo := (square_zero_iff v).mp hvz
  have hsum := v.initial_proj.add v.final_proj hvo
  have hsump : v.initial+v.final ≤ p := by
    apply (hsum.le_iff_mul_eq_right hp).mpr
    rw [mul_add,(v.initial_proj.le_iff_mul_eq_right hp).mp v.init_le,
      (v.final_proj.le_iff_mul_eq_right hp).mp v.final_le]
  let r := p-(v.initial+v.final)
  have hr : IsStarProjection r := (hsum.le_iff_sub hp).mp hsump
  have hrI : r ≤ p-v.initial := by dsimp [r]; exact sub_le_sub_left (le_add_of_nonneg_right v.final_proj.nonneg) p
  have hrF : r ≤ p-v.final := by dsimp [r]; exact sub_le_sub_left (le_add_of_nonneg_left v.initial_proj.nonneg) p
  have hr0 : r=0 := by
    by_contra hh
    obtain ⟨u,huo,hu0⟩ := orthogonal_pair e hII hr hh
    let U : CornerIso (p-v.initial) (p-v.final) :=
      ⟨(u:M),u.init_proj,u.absorb,u.init_le.trans hrI,u.final_le.trans hrF⟩
    obtain ⟨w,hw,hvw⟩ := add_orthogonal hp hp v U
    have hvu : (v:M)*(u:M)=0 := by
      have hIF : v.initial*u.final=0 := projection_mul_zero_of_le_sub hp v.initial_proj
        u.final_proj v.init_le (u.final_le.trans hrI)
      calc
        _=((v:M)*v.initial)*(u.final*(u:M)) := by rw [v.mul_initial,u.final_mul]
        _=0 := by simp only [mul_assoc,←mul_assoc v.initial u.final (u:M),hIF,zero_mul,mul_zero]
    have huv : (u:M)*(v:M)=0 := by
      have hFI : v.final*u.initial=0 := projection_mul_zero_of_le_sub hp v.final_proj
        u.initial_proj v.final_le (u.init_le.trans hrF)
      have hIF : u.initial*v.final=0 := by
        simpa only [star_mul,v.final_proj.isSelfAdjoint.star_eq,u.initial_proj.isSelfAdjoint.star_eq,
          star_zero] using congrArg star hFI
      calc
        _=((u:M)*u.initial)*(v.final*(v:M)) := by rw [u.mul_initial,v.final_mul]
        _=0 := by simp only [mul_assoc,←mul_assoc u.initial v.final (v:M),hIF,zero_mul,mul_zero]
    have hwz : (w:M)*(w:M)=0 := by
      change (w:M)=(v:M)+(u:M) at hw
      rw [hw,add_mul,mul_add,mul_add,hvz,hvu,huv,(square_zero_iff u).mpr huo]
      simp
    have he : w=v := le_antisymm (hmax w hwz hvw) hvw
    have hh : (u:M)=0 := by
      change (w:M)=(v:M)+(u:M) at hw
      rw [he] at hw
      exact (add_left_cancel (show (v:M)+(u:M)=(v:M)+0 by simpa using hw.symm))
    exact hu0 hh
  exact ⟨v,hvo,(sub_eq_zero.mp hr0).symm⟩
end PopaTypeII

end

end OAI
