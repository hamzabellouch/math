import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.PartialRepresentations

namespace OAI

/-! Representation limits for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaPatching.Rep
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaCorners
variable {G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
@[ext] lemma ext {v w : Rep G M} (h : ∀ g, v g=w g) : v=w := by
  cases v; cases w; simp_all [Rep.mk.injEq,funext_iff]

instance : PartialOrder (Rep G M) where
  le v w := v.support ≤ w.support ∧ ∀ g, w g*v.support=v g
  le_refl v := ⟨le_rfl,v.mul_support⟩
  le_trans v w z hvw hwz := by
    refine ⟨hvw.1.trans hwz.1,fun g => ?_⟩
    have hp := (v.support_projection.le_iff_mul_eq_right w.support_projection).mp hvw.1
    calc
      z g*v.support = z g*(w.support*v.support) := by rw [hp]
      _ = v g := by rw [←mul_assoc,hwz.2,hvw.2]
  le_antisymm v w hvw hwv := by
    apply ext; intro g
    have hp := le_antisymm hvw.1 hwv.1
    simpa only [hp,w.mul_support] using (hvw.2 g).symm

lemma le_def {v w : Rep G M} : v ≤ w ↔
    v.support ≤ w.support ∧ ∀ g, w g*v.support=v g := Iff.rfl

lemma support_mul_of_le {v w : Rep G M} (h : v ≤ w) (g : G) :
    v.support*w g=v g := by
  have hh := congrArg star (h.2 g⁻¹)
  simpa only [star_mul,v.support_projection.isSelfAdjoint.star_eq,
    v.inv,w.inv,star_star] using hh

def toCorner (v : Rep G M) (g : G) : CornerIso (1:M) 1 where
  val := v g
  init_proj := by rw [v.star_mul_self]; exact v.support_projection
  absorb := by rw [v.star_mul_self,v.mul_support]
  init_le := by rw [v.star_mul_self]; exact v.support_projection.le_one
  final_le := by rw [v.mul_star_self]; exact v.support_projection.le_one

@[simp] lemma toCorner_val (v : Rep G M) (g : G) : (toCorner v g : M)=v g := rfl
@[simp] lemma toCorner_initial (v : Rep G M) (g : G) : (toCorner v g).initial=v.support :=
  v.star_mul_self g
lemma toCorner_mono (g : G) : Monotone (fun v : Rep G M => toCorner v g) := by
  intro v w h
  rw [CornerIso.le_def,toCorner_initial,toCorner_initial]
  exact ⟨h.1,h.2 g⟩

def rank (τ : M →ₚ[ℂ] ℂ) (v : Rep G M) : ℝ := (τ v.support).re
lemma rank_mono (τ : M →ₚ[ℂ] ℂ) : Monotone (rank τ : Rep G M → ℝ) := by
  intro v w h
  exact Complex.re_le_re (τ.monotone h.1)

lemma le_of_comparable_rank_le (τ : M →ₚ[ℂ] ℂ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) {v w : Rep G M}
    (hc : v ≤ w ∨ w ≤ v) (ht : rank τ v ≤ rank τ w) : v ≤ w := by
  rcases hc with h|h
  · exact h
  · have he : v=w := by
      apply ext; intro g
      have hh := CornerIso.le_of_comparable_rank_le τ hfaith
        (Or.inr (toCorner_mono g h)) (show CornerIso.rank τ (toCorner v g) ≤
          CornerIso.rank τ (toCorner w g) by simpa only [CornerIso.rank,toCorner_initial,rank] using ht)
      have he := le_antisymm hh (toCorner_mono g h)
      exact congrArg CornerIso.val he
    exact he.le

section Dual
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

include e hτ htr hfaith in
lemma monotone_limit (v : ℕ → Rep G M) (hv : Monotone v) :
    ∃ w : Rep G M, (∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) ∧
      (∀ n, v n ≤ w) ∧ (∀ z, (∀ n, v n ≤ z) → w ≤ z) := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  have hex (g : G) := CornerIso.monotone_limit e τ hτ htr hfaith
    (IsStarProjection.one M) (IsStarProjection.one M) (fun n => toCorner (v n) g)
    ((toCorner_mono g).comp hv)
  choose w hwt hwn hwl using hex
  have hmul (g h : G) : (w (g*h):M)=(w g:M)*(w h:M) := by
    apply GNSTendsto.unique τ hfaith (hwt (g*h))
    simpa only [toCorner_val,←(v _).mul] using (hwt g).mul τ htr (hwt h) 1 (fun n => (v n).norm_le g)
  have hinv (g : G) : (w g⁻¹:M)=star (w g:M) := by
    apply GNSTendsto.unique τ hfaith (hwt g⁻¹)
    simpa only [toCorner_val,←(v _).inv] using (hwt g).star τ htr
  let W : Rep G M := ⟨fun g => (w g:M),hmul,hinv⟩
  have hW (g : G) : (w g).initial=W.support :=
    (W.star_mul_self g)
  refine ⟨W,hwt,?_,?_⟩
  · intro n
    refine ⟨?_,fun g => by simpa only [toCorner_initial,toCorner_val] using (hwn g n).2⟩
    have hh := (hwn 1 n).1
    simpa only [toCorner_initial,hW] using hh
  · intro z hz
    have hh (g : G) := hwl g (toCorner z g) (fun n => toCorner_mono g (hz n))
    refine ⟨?_,fun g => ?_⟩
    · simpa only [hW,toCorner_initial] using (hh 1).1
    · simpa only [hW,toCorner_val] using (hh g).2

include e hτ hfaith in
lemma rank_tendsto {v : ℕ → Rep G M} {w : Rep G M}
    (ht : ∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) :
    Tendsto (fun n => rank τ (v n)) atTop (𝓝 (rank τ w)) := by
  have hL := (HochschildSakai.abstract_multiplication_normal e).1
  exact Complex.continuous_re.tendsto _ |>.comp
    (trace_predual_tendsto e τ hτ (predual_tendsto_of_preGNS e τ hL hτ hfaith 1
      (fun n => (v n).norm_le 1) (ht 1)))

include e hτ htr hfaith in

lemma exists_maximal_closed (P : Rep G M → Prop) (hzero : P Rep.zero)
    (hclosed : ∀ (v : ℕ → Rep G M) (w : Rep G M),
      (∀ n, P (v n)) → (∀ g, GNSTendsto τ (fun n => v n g) atTop (w g)) → P w) :
    ∃ v : Rep G M, P v ∧ ∀ w : Rep G M, P w → v ≤ w → w ≤ v := by
  classical
  have hu (c : Set (Rep G M)) (hc : c ⊆ {v | P v})
      (hchain : IsChain (· ≤ ·) c) (hne : c.Nonempty) :
      ∃ w, P w ∧ ∀ v ∈ c, v ≤ w := by
    let T : Set ℝ := rank τ '' c
    have hTne : T.Nonempty := Set.Nonempty.image _ hne
    have hTbd : BddAbove T := by
      refine ⟨(τ 1).re,?_⟩
      rintro _ ⟨v,hv,rfl⟩
      exact Complex.re_le_re (τ.monotone v.support_projection.le_one)
    obtain ⟨t,htm,_htL,htt,htc⟩ := (isLUB_csSup hTne hTbd).exists_seq_monotone_tendsto hTne
    choose a ha hat using htc
    change ∀ n, rank τ (a n)=t n at hat
    have ham : Monotone a := by
      intro m n hmn
      apply le_of_comparable_rank_le τ hfaith (hchain.total (ha m) (ha n))
      rw [hat,hat]; exact htm hmn
    obtain ⟨w,hwt,hwn,hwl⟩ := monotone_limit e τ hτ htr hfaith a ham
    have hwr : rank τ w=sSup T := by
      apply tendsto_nhds_unique (rank_tendsto e τ hτ hfaith hwt)
      simpa only [hat] using htt
    refine ⟨w,hclosed a w (fun n => hc (ha n)) hwt,fun v hv => ?_⟩
    by_cases hex : ∃ n, v ≤ a n
    · obtain ⟨n,hn⟩ := hex
      exact hn.trans (hwn n)
    · have haw : ∀ n, a n ≤ v := fun n =>
        (hchain.total (ha n) hv).resolve_right (fun h => hex ⟨n,h⟩)
      apply le_of_comparable_rank_le τ hfaith (Or.inr (hwl v haw))
      rw [hwr]
      exact le_csSup hTbd ⟨v,hv,rfl⟩
  obtain ⟨v,hv,hmax⟩ := zorn_le_nonempty₀ {v | P v}
    (fun c hc hchain y hy => hu c hc hchain ⟨y,hy⟩) Rep.zero hzero
  exact ⟨v,hmax.1,fun w hw hle => hmax.2 hw hle⟩
end Dual
end PopaPatching.Rep

end

end OAI
