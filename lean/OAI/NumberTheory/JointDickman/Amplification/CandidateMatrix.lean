import OAI.NumberTheory.JointDickman.Amplification.IndependentRootMaximum

namespace OAI

/-! # Symmetric matrices assembled from unordered candidate edges -/

namespace JointDickman
open Finset

theorem realBilinear_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : ι → κ → κ → ℝ) (f g : κ → ℝ) :
    realBilinear (fun i k => ∑ e, K e i k) f g = ∑ e, realBilinear (K e) f g := by
  unfold realBilinear
  simp only [sum_mul]
  calc
    _ = ∑ i, ∑ e, ∑ k, K e i k*f i*g k := by
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
    _ = _ := by rw [sum_comm]

noncomputable def candidateMatrix {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (i k : κ) : ℝ :=
  ∑ e, ((if i = row e then if k = col e then v e else 0 else 0)+
    (if i = col e then if k = row e then v e else 0 else 0))

theorem candidateMatrix_bilinear {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) (f g : κ → ℝ) :
    realBilinear (candidateMatrix row col v) f g =
      ∑ e, v e*(f (row e)*g (col e)+f (col e)*g (row e)) := by
  unfold candidateMatrix
  rw [realBilinear_sum]
  apply sum_congr rfl
  intro e _
  simp [realBilinear,add_mul,ite_mul,sum_add_distrib]; ring

abbrev EdgeCutTest (κ : Type*) := ((κ → Bool) × (κ → Bool)) × Bool

noncomputable def edgeCutCoefficient {ι κ : Type*} (row col : ι → κ)
    (s : EdgeCutTest κ) (e : ι) : ℝ :=
  cutSign s.2*(cutSign (s.1.1 (row e))*cutSign (s.1.2 (col e))+
    cutSign (s.1.1 (col e))*cutSign (s.1.2 (row e)))

theorem edgeCutCoefficient_bound {ι κ : Type*} (row col : ι → κ)
    (s : EdgeCutTest κ) (e : ι) : |edgeCutCoefficient row col s e| ≤ 2 := by
  unfold edgeCutCoefficient
  rw [abs_mul,abs_cutSign,one_mul]
  have h := abs_add_le
    (cutSign (s.1.1 (row e))*cutSign (s.1.2 (col e)))
    (cutSign (s.1.1 (col e))*cutSign (s.1.2 (row e)))
  simpa only [abs_mul,abs_cutSign,one_mul,one_add_one_eq_two] using h

theorem candidateMatrix_cutMaximum_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (row col : ι → κ) (v : ι → ℝ) :
    kernelCutMaximum (candidateMatrix row col v) ≤
      finiteFamilyMaximum (fun s : EdgeCutTest κ => fun _ : Unit =>
        ∑ e, edgeCutCoefficient row col s e*v e) () := by
  classical
  apply kernelCutMaximum_le
  intro s t
  let b := decide (0 ≤ realBilinear (candidateMatrix row col v)
    (fun i => cutSign (s i)) (fun i => cutSign (t i)))
  have hb : cutSign b * realBilinear (candidateMatrix row col v)
      (fun i => cutSign (s i)) (fun i => cutSign (t i)) =
      |realBilinear (candidateMatrix row col v) (fun i => cutSign (s i)) (fun i => cutSign (t i))| := by
    have hscalar (x : ℝ) : cutSign (decide (0 ≤ x))*x = |x| := by
      by_cases hx : 0 ≤ x
      · simp [cutSign,hx,abs_of_nonneg hx]
      · simp [cutSign,hx,abs_of_neg (lt_of_not_ge hx)]
    exact hscalar _
  have he : (∑ e, edgeCutCoefficient row col ((s,t),b) e*v e) =
      cutSign b*realBilinear (candidateMatrix row col v) (fun i => cutSign (s i))
        (fun i => cutSign (t i)) := by
    rw [candidateMatrix_bilinear,mul_sum]
    apply sum_congr rfl
    intro e _
    dsimp [edgeCutCoefficient]
    ring
  rw [← hb,← he]
  exact le_sup' (fun q : EdgeCutTest κ => ∑ e, edgeCutCoefficient row col q e*v e)
    (mem_univ ((s,t),b))

end JointDickman

end OAI
