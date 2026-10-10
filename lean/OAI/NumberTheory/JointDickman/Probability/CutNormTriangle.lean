import OAI.NumberTheory.JointDickman.Amplification.CandidateRootErrorCap

namespace OAI

/-! # Triangle inequalities for the finite cut norm -/

namespace JointDickman
open Finset Classical

theorem kernelCutMaximum_bilinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : ι → ι → ℝ) (s t : ι → Bool) :
    |realBilinear K (fun i => cutSign (s i)) (fun i => cutSign (t i))| ≤ kernelCutMaximum K :=
  le_sup' (fun st : (ι → Bool) × (ι → Bool) =>
    |realBilinear K (fun i => cutSign (st.1 i)) (fun i => cutSign (st.2 i))|) (mem_univ (s,t))

theorem kernelCutNorm_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K L : ι → ι → ℝ) :
    kernelCutNorm (fun i k => K i k+L i k) ≤ kernelCutNorm K+kernelCutNorm L := by
  unfold kernelCutNorm
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply kernelCutMaximum_le
  intro s t
  have he : realBilinear (fun i k => K i k+L i k) (fun i => cutSign (s i)) (fun i => cutSign (t i)) =
      realBilinear K (fun i => cutSign (s i)) (fun i => cutSign (t i))+
        realBilinear L (fun i => cutSign (s i)) (fun i => cutSign (t i)) := by
    simp [realBilinear,add_mul,sum_add_distrib]
  rw [he]
  exact (abs_add_le _ _).trans
    (add_le_add (kernelCutMaximum_bilinear K s t) (kernelCutMaximum_bilinear L s t))

theorem kernelCutNorm_sub_triangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K A L : ι → ι → ℝ) :
    kernelCutNorm (fun i k => K i k-L i k) ≤
      kernelCutNorm (fun i k => K i k-A i k)+kernelCutNorm (fun i k => A i k-L i k) := by
  convert kernelCutNorm_add (fun i k => K i k-A i k) (fun i k => A i k-L i k) using 1
  congr 1
  funext i k
  ring

theorem kernelCutNorm_zero {ι : Type*} [Fintype ι] [DecidableEq ι] :
    kernelCutNorm (fun _ _ : ι => (0 : ℝ)) = 0 := by
  simp [kernelCutNorm,kernelCutMaximum,realBilinear]

end JointDickman

end OAI
