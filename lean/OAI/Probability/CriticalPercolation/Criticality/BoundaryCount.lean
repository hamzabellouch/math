import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.Weight
import OAI.Probability.CriticalPercolation.GraphGeometry.Link2

namespace OAI

section
section CurrentModule2
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

lemma expect_exposure_finiteRange {I A B : Type*} [Fintype I] [Fintype A]
    (w : I → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (r : (I → A) → B) (D : B → Set I)
    (hr : ∀ b, DependsOn (fun ω => r ω = b) (D b))
    (f : B → (I → A) → ℝ) (hf : ∀ b, DependsOn (f b) (D b)ᶜ) :
    expect w (fun ω => f (r ω) ω) =
      expect w (fun ω => expect w (f (r ω))) := by
  let : Fintype (Set.range r) := (Set.finite_range r).fintype
  let r' : (I → A) → Set.range r := fun ω => ⟨r ω,ω,rfl⟩
  exact expect_exposure w hw r' (fun b => D b.val)
    (fun b ω ω' hω => by
      apply propext
      simpa only [r',Subtype.ext_iff] using (hr b.val hω).to_iff)
    (fun b => f b.val) (fun b => hf b.val)

variable {V E : Type*} [Fintype E] (G : BondGraph V E)

lemma spatialMarkov (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (T : Set V) (F : Set V → SimpleGraph V → ℝ) :
    expect w (fun ω => F (roots (G.openGraph ω) T)
        (delete (G.openGraph ω) (roots (G.openGraph ω) T))) =
      expect w (fun ω => expect w (fun ω' => F (roots (G.openGraph ω) T)
        (delete (G.openGraph ω') (roots (G.openGraph ω) T)))) := by
  refine expect_exposure_finiteRange w hw
    (fun ω => roots (G.openGraph ω) T) G.incidentEdges
    (G.dependsOn_exact_roots T)
    (fun R ω => F R (delete (G.openGraph ω) R)) ?_
  intro R ω ω' hω
  exact congrArg (F R) (G.delete_openGraph_dependsOn R hω)

def boundaryCount (o : V) (R : Set V) (H : SimpleGraph V) : ℝ :=
  ∑ e, if boundaryReach G R H o e then 1 else 0

def boundaryFlux (p : ℝ) (o : V) (R : Set V) : ℝ :=
  p * expect (fun _ : E => weight p)
    (fun ω => boundaryCount G o R (delete (G.openGraph ω) R))

omit [Fintype E] in
lemma closedPivot_reachesTarget (o : V) (T : Set V) (ω : Set E) (e : E) :
    closedPivot (reachesTarget G o T) e ω ↔
      o ∉ roots (G.openGraph ω) T ∧
      boundaryReach G (roots (G.openGraph ω) T)
        (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e := by
  constructor
  · rintro ⟨_,ho,he⟩
    exact ⟨ho,(target_creating_iff G o T ω e ho).mp he⟩
  · rintro ⟨ho,he⟩
    exact ⟨boundaryReach_closed G o T ω e he,ho,
      (target_creating_iff G o T ω e ho).mpr he⟩

lemma sum_closedPivot_eq (p : ℝ) (o : V) (T : Set V) :
    ∑ e, probability p (closedPivot (reachesTarget G o T) e) =
      expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          expect (fun _ : E => weight p) (fun ω' => boundaryCount G o
            (roots (G.openGraph ω) T)
            (delete (G.openGraph ω') (roots (G.openGraph ω) T))) else 0) := by
  have hs := spatialMarkov G (fun _ : E => weight p) (fun _ => weight_sum p)
    T (fun R H => if o ∉ R then boundaryCount G o R H else 0)
  unfold probability
  rw [← expect_sum]
  calc
    _ = expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          boundaryCount G o (roots (G.openGraph ω) T)
            (delete (G.openGraph ω) (roots (G.openGraph ω) T)) else 0) := by
      congr 1
      funext ω
      have he (e : E) : closedPivot (reachesTarget G o T) e ω ↔
          o ∉ roots (G.openGraph ω) T ∧ boundaryReach G (roots (G.openGraph ω) T)
            (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e :=
        closedPivot_reachesTarget G o T ω e
      simp only [he]
      by_cases ho : o ∈ roots (G.openGraph ω) T
      · simp [ho]
      · simp [ho,boundaryCount]
    _ = _ := by
      rw [hs]
      congr 1
      funext ω
      split_ifs <;> simp only [expect_zero]

lemma exposedFlux_identity (p : ℝ) (o : V) (T : Set V) :
    p * (∑ e, probability p (closedPivot (reachesTarget G o T) e)) =
      expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          boundaryFlux G p o (roots (G.openGraph ω) T) else 0) := by
  rw [sum_closedPivot_eq, ← expect_const_mul]
  congr 1
  funext ω
  split_ifs <;> simp only [boundaryFlux,mul_zero]

theorem derivative_identity {p : ℝ} (hp : p ∈ Ioo 0 1) (o : V) (T : Set V) :
    p * (1-p) * deriv (fun q => probability q (reachesTarget G o T)) p =
      expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          boundaryFlux G p o (roots (G.openGraph ω) T) else 0) := by
  have hd := hasDerivAt_probability_closedPivot hp (reachesTarget G o T)
    (fun _ _ h => reachesTarget_mono G o T h)
  rw [hd.deriv, ← exposedFlux_identity]
  field_simp [(sub_pos.mpr hp.2).ne']

theorem differential_inequality {p a : ℝ} (hp : p ∈ Ioo 0 1) (o : V) (T : Set V)
    (hflux : ∀ R : Set V, T ⊆ R → o ∉ R → a ≤ boundaryFlux G p o R) :
    a * (1-probability p (reachesTarget G o T)) ≤
      p * (1-p) * deriv (fun q => probability q (reachesTarget G o T)) p := by
  rw [derivative_identity G hp o T]
  have hcomp : expect (fun _ : E => weight p)
      (fun ω => if o ∉ roots (G.openGraph ω) T then (1:ℝ) else 0) =
      1-probability p (reachesTarget G o T) := by
    calc
      _ = expect (fun _ : E => weight p) (fun ω =>
          1-(if reachesTarget G o T ω then (1:ℝ) else 0)) := by
        congr 1
        funext ω
        unfold reachesTarget
        by_cases ho : o ∈ roots (G.openGraph ω) T <;> simp [ho]
      _ = _ := by
        rw [expect_sub,expect_const _ (fun _ => weight_sum p)]
        rfl
  rw [← hcomp, ← expect_const_mul]
  apply expect_mono (fun _ b => weight_nonneg ⟨hp.1.le,hp.2.le⟩ b)
  intro ω
  by_cases ho : o ∈ roots (G.openGraph ω) T
  · simp [ho]
  · simp only [ho,not_false_eq_true,ite_true,mul_one]
    exact hflux (roots (G.openGraph ω) T) (roots_self _ _) ho

end CriticalPercolation.Sharpness
end
end CurrentModule2

end

end OAI
