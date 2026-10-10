import Mathlib
import OAI.Probability.SKGap.Matrix.RankNorm
import OAI.Probability.SKGap.Brownian.LogDetMesh
import OAI.Probability.SKGap.Stability.LogDetUniformMean

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology

theorem actual_logdet_uniform {j ε : ℝ} (hj : 0 < j) (hj1 : j < 1) (hε : 0 < ε) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ → ∃ N : ℕ, 0 < N ∧
      ∀ n : ℕ, N ≤ n →
        (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
          {g | ∃ a : Fin n → ℝ, (∀ i,0 ≤ a i) ∧ (∀ i,a i ≤ 1) ∧
            j*(coordAverage a)^2+ε < LogDet.regularizedLogDet γ
              (logPath (j*coordAverage a) a (goeMatrix (j/(n:ℝ)) g) 1)} ≤
          4*Real.exp (-min 1 (1/(π^2*j))*(n:ℝ)) := by
  classical
  obtain ⟨B,hB,hmean⟩ := actual_logdet_mean hj hj1
  refine ⟨ε/(4*(B^2+1)),by positivity,?_⟩
  intro γ hγ hγ₀
  obtain ⟨C,hC,N₀,hN₀,hm⟩ := hmean γ hγ
  have hγB : γ*B^2 ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(B^2+1))).mp hγ₀
    nlinarith
  let R := 2*sqrt j+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let K := (2*j+R)/sqrt γ+2*j
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ := ε/(4*(K+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKδ : K*δ ≤ ε/4 := by
    have hh : δ*(4*(K+1))=ε := div_mul_cancel₀ ε (ne_of_gt (by positivity : 0 < 4*(K+1)))
    nlinarith
  obtain ⟨s,hs,hcover⟩ := scalar_cube_net hδ
  let q := γ*(ε/4)^2/(π^2*j)
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge (4*C/ε)
  obtain ⟨N₂,hN₂⟩ := exists_nat_ge (((s.card:ℝ)+1)/q)
  refine ⟨max N₀ (max N₁ N₂),hN₀.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hn₀ := (le_max_left N₀ (max N₁ N₂)).trans hn
  have hn₁ := (le_max_left N₁ N₂).trans ((le_max_right N₀ (max N₁ N₂)).trans hn)
  have hn₂ := (le_max_right N₁ N₂).trans ((le_max_right N₀ (max N₁ N₂)).trans hn)
  have hnpos := hN₀.trans_le hn₀
  have hnreal : (0:ℝ) < n := Nat.cast_pos.mpr hnpos
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  have hCn : C/(n:ℝ) ≤ ε/4 := by
    have hh := hN₁.trans (Nat.cast_le.mpr hn₁)
    have hh' := (div_le_iff₀ hε).mp hh
    apply (div_le_iff₀ hnreal).mpr
    nlinarith
  let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)
  let M := fun g : MatrixCoordinates (Fin n) → ℝ => goeMatrix (j/(n:ℝ)) g
  let T := {g | ∃ v : Fin n → s, j*(coordAverage (fun i => (v i:ℝ)))^2+ε/2+ε/4 <
        LogDet.regularizedLogDet γ (logPath (j*coordAverage (fun i => (v i:ℝ)))
          (fun i => (v i:ℝ)) (M g) 1)}
  let U := {g | R < opNorm (M g)}
  have hT : μ.real T ≤ 2*Real.exp (-(n:ℝ)) := by
    apply (logdet_mesh_tail hj hγ (by positivity : 0 ≤ ε/4) hnpos s hs ?_).trans
    · have hh := product_mesh_absorption hq s.card n (hN₂.trans (Nat.cast_le.mpr hn₂))
      have he : -γ*(n:ℝ)^2*(ε/4)^2/(π^2*j)= -q*(n:ℝ)^2 := by dsimp only [q]; ring
      simpa only [he] using hh
    · intro a ha ha1
      have hh := hm n hn₀ a ha ha1
      have he : (j/(n:ℝ))*∑ i,a i=j*coordAverage a := by simp only [coordAverage,Fintype.card_fin]; ring
      rw [he] at hh
      change (∫ g, LogDet.regularizedLogDet γ (logPath (j*coordAverage a) a (M g) 1) ∂μ) ≤ _
      have heavg : (∑ i,a i)/(n:ℝ)=coordAverage a := by simp only [coordAverage,Fintype.card_fin]
      rw [heavg] at hh
      linarith
  have hU : μ.real U ≤ 2*Real.exp (-(n:ℝ)/(π^2*j)) := by
    change (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | 2*sqrt j+1 < ‖matrixOperator (goeMatrix (j/(n:ℝ)) g)‖} ≤ _
    simpa only [one_pow,_root_.neg_one_mul,Fintype.card_fin] using
      (goe_norm_tail (ι := Fin n) hj (by norm_num : (0:ℝ) ≤ 1))
  have hsub : {g | ∃ a : Fin n → ℝ, (∀ i,0 ≤ a i) ∧ (∀ i,a i ≤ 1) ∧
      j*(coordAverage a)^2+ε < LogDet.regularizedLogDet γ (logPath (j*coordAverage a) a (M g) 1)} ⊆ T ∪ U := by
    rintro g ⟨a,ha,ha1,hbad⟩
    by_contra hg
    have hnot := not_or.mp hg
    have hop : opNorm (M g) ≤ R := le_of_not_gt hnot.2
    have hnet (v : Fin n → s) : LogDet.regularizedLogDet γ (logPath (j*coordAverage (fun i => (v i:ℝ)))
        (fun i => (v i:ℝ)) (M g) 1) ≤ j*(coordAverage (fun i => (v i:ℝ)))^2+(ε/2+ε/4) := by
      have hh : ¬ j*(coordAverage (fun i => (v i:ℝ)))^2+ε/2+ε/4 <
          LogDet.regularizedLogDet γ (logPath (j*coordAverage (fun i => (v i:ℝ)))
            (fun i => (v i:ℝ)) (M g) 1) := fun hv => hnot.1 ⟨v,hv⟩
      linarith [le_of_not_gt hh]
    have hh := logdet_cube_net_transfer hj.le hδ hR hγ s hs hcover hop hnet ha ha1
    change LogDet.regularizedLogDet γ (logPath (j*coordAverage a) a (M g) 1) ≤
      j*(coordAverage a)^2+(ε/2+ε/4)+K*δ at hh
    linarith
  have hb := (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le T U).trans (add_le_add hT hU))
  apply hb.trans
  have e₁ : Real.exp (-(n:ℝ)) ≤ Real.exp (-min 1 (1/(π^2*j))*(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr (min_le_left 1 (1/(π^2*j))))]
  have e₂ : Real.exp (-(n:ℝ)/(π^2*j)) ≤ Real.exp (-min 1 (1/(π^2*j))*(n:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_right 1 (1/(π^2*j))) (Nat.cast_nonneg n)
    simp only [div_eq_mul_inv,_root_.one_mul] at hh ⊢
    nlinarith
  linarith
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Matrix.Norms.Frobenius Topology

theorem actual_simultaneous_logdet {j ε : ℝ} (hj : 0 < j) (hj1 : j < 1) (hε : 0 < ε) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ → ∀ r₀ : ℕ, ∀ M₂ : ℝ,
      ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
        (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
          {g | ∃ a : Fin n → ℝ, (∀ i,0 ≤ a i) ∧ (∀ i,a i ≤ 1) ∧
            ∃ E : Matrix (Fin n) (Fin n) ℝ, E.rank ≤ r₀ ∧ opNorm E ≤ M₂ ∧
              j*(coordAverage a)^2+ε < LogDet.regularizedLogDet γ
                (1+((j*coordAverage a) • 1-goeMatrix (j/(n:ℝ)) g)*diagonal a+E)} ≤
          4*Real.exp (-min 1 (1/(π^2*j))*(n:ℝ)) := by
  obtain ⟨γ₀,hγ₀,hbound⟩ := actual_logdet_uniform hj hj1 (half_pos hε)
  refine ⟨γ₀,hγ₀,?_⟩
  intro γ hγ hγle r₀ M₂
  obtain ⟨N₀,hN₀,hb⟩ := hbound γ hγ hγle
  let D := max 0 M₂
  have hD : 0 ≤ D := le_max_left _ _
  obtain ⟨N₁,hN₁⟩ := exists_nat_ge ((2*D*sqrt (r₀:ℝ)/ε)^2/γ)
  refine ⟨max N₀ N₁,hN₀.trans_le (le_max_left _ _),?_⟩
  intro n hn
  have hn₀ := (le_max_left N₀ N₁).trans hn
  have hn₁ := (le_max_right N₀ N₁).trans hn
  have hnpos := hN₀.trans_le hn₀
  have hnreal : (0:ℝ) < n := Nat.cast_pos.mpr hnpos
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  have hroot : 2*D*sqrt (r₀:ℝ)/ε ≤ sqrt ((n:ℝ)*γ) := by
    apply (sq_le_sq₀ (by positivity) (sqrt_nonneg _)).mp
    rw [sq_sqrt (by positivity)]
    have hh := (div_le_iff₀ hγ).mp (hN₁.trans (Nat.cast_le.mpr hn₁))
    exact hh
  have hpert : D*sqrt (r₀:ℝ)/sqrt ((n:ℝ)*γ) ≤ ε/2 := by
    apply (div_le_iff₀ (sqrt_pos.mpr (mul_pos hnreal hγ))).mpr
    have hh := (div_le_iff₀ hε).mp hroot
    nlinarith
  apply (measureReal_mono (s₂ := {g | ∃ a : Fin n → ℝ, (∀ i,0 ≤ a i) ∧ (∀ i,a i ≤ 1) ∧
      j*(coordAverage a)^2+ε/2 < LogDet.regularizedLogDet γ
        (logPath (j*coordAverage a) a (goeMatrix (j/(n:ℝ)) g) 1)}) ?_ (measure_ne_top _ _)).trans (hb n hn₀)
  rintro g ⟨a,ha,ha1,E,hr,hE,hbad⟩
  refine ⟨a,ha,ha1,?_⟩
  let W := goeMatrix (j/(n:ℝ)) g
  let L := 1+((j*coordAverage a) • 1-W)*diagonal a
  have htr : Lᵀ=logPath (j*coordAverage a) a W 1 := by
    have hW : Wᵀ=W := goeMatrix_symm (j/(n:ℝ)) g
    simp only [L,transpose_add,transpose_one,transpose_mul,transpose_sub,transpose_smul,
      diagonal_transpose,hW,logPath,one_pow,one_mul,one_smul,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one]
    abel
  have hf : LogDet.regularizedLogDet γ (L+E)=
      LogDet.regularizedLogDet γ (logPath (j*coordAverage a) a W 1+Eᵀ) := by
    rw [← regularizedLogDet_transpose (ne_of_gt hγ) (L+E),transpose_add,htr]
  have hh := (abs_le.mp (logdet_rank_perturbation hγ hD
    (logPath (j*coordAverage a) a W 1) Eᵀ
    (by simpa only [Matrix.rank_transpose] using hr)
    (by rw [opNorm_transpose]; exact hE.trans (le_max_right _ _)))).2
  simp only [Fintype.card_fin] at hh
  change j*(coordAverage a)^2+ε < LogDet.regularizedLogDet γ (L+E) at hbad
  rw [hf] at hbad
  linarith
end SKGap
end
end

end OAI
