import Mathlib
import OAI.Probability.SKGap.Stability.RootDiagonalTransfer
import OAI.Probability.SKGap.Matrix.GOESubmatrix

namespace OAI

section

noncomputable section
namespace SKGap.ObservationBridge
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

lemma absorb_linear_exponential {b : ℝ} (hb : 0 < b) :
    ∃ N : ℕ, ∀ n ≥ N,
      2*(n:ℝ)*exp (-b*(n:ℝ)) ≤ exp (-(b/2)*(n:ℝ)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (16/b^2)
  refine ⟨N,fun n hn=>?_⟩
  have hnR : 16/b^2 ≤ (n:ℝ) := hN.trans (Nat.cast_le.mpr hn)
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hbn : 16 ≤ (n:ℝ)*b^2 := (div_le_iff₀ (sq_pos_of_pos hb)).mp hnR
  have hmul := mul_le_mul_of_nonneg_right hbn hn0
  have he := Real.pow_div_factorial_le_exp ((b/2)*(n:ℝ)) (by positivity) 2
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at he
  have hhead : 2*(n:ℝ) ≤ exp ((b/2)*(n:ℝ)) := by nlinarith
  calc
    _ ≤ exp ((b/2)*(n:ℝ))*exp (-b*(n:ℝ)) :=
      mul_le_mul_of_nonneg_right hhead (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

lemma shifted_goe_diagonal_tail {j δ : ℝ} (hj : 0 < j) (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) (hmean : j/(n:ℝ) ≤ δ/2) :
    (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ∃ i, δ < |plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i|} ≤
      2*(n:ℝ)*exp (-(δ^2/(32*j))*(n:ℝ)) := by
  have hr : 0 < j/(n:ℝ) := div_pos hj (Nat.cast_pos.mpr hn)
  have hs : {g : MatrixCoordinates (Fin n)→ℝ | ∃ i,
      δ < |plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i|} ⊆
      {g | ∃ i, δ/2 < |goeMatrix (j/(n:ℝ)) g i i|} := by
    rintro g ⟨i,hi⟩
    refine ⟨i,?_⟩
    have he : plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i =
        goeMatrix (j/(n:ℝ)) g i i+j/(n:ℝ) := by
      simp [plantedInteraction,Matrix.vecMulVec]
    rw [he] at hi
    have hh := abs_add_le (goeMatrix (j/(n:ℝ)) g i i) (j/(n:ℝ))
    rw [abs_of_pos hr] at hh
    linarith
  apply (measureReal_mono hs (measure_ne_top _ _)).trans
  have hh := goe_diagonal_tail (ι:=Fin n) hr (half_pos hδ).le
  have he : -(δ/2)^2/(8*(j/(n:ℝ))) = -(δ^2/(32*j))*(n:ℝ) := by
    field_simp
    ring
  simpa only [Fintype.card_fin,he] using hh

def erasedPlantedRootBad (n : ℕ) (j A K ε c ρ t : ℝ) :
    Set ((MatrixCoordinates (Fin n)→ℝ) × (Fin n→ℝ)) :=
  {p | (∀ z : Field n, vectorNorm
      (eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1))*ᵥz) ≤ K*vectorNorm z) ∧
    rootBad j A ε c ρ (eraseDiagonal (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1)))
      (fun i=>t+p.2 i)}

lemma erased_planted_probability {n : ℕ} {j A K ε c ρ δ a t : ℝ}
    (hj : 0 < j) (hA : 0 ≤ A) (hδ : 0 < δ) (hn : 0 < n)
    (hδρ : δ ≤ ρ/2) (hδc : A*δ ≤ c/2) (hmean : j/(n:ℝ) ≤ δ/2)
    (hp : ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
       (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
        (plantedRootBad n j A K ε c ρ t) ≤ exp (-a*(n:ℝ))) :
    ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
       (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
        (erasedPlantedRootBad n j A (K-δ) ε (c/2) (ρ/2) t) ≤
      exp (-a*(n:ℝ))+2*(n:ℝ)*exp (-(δ^2/(32*j))*(n:ℝ)) := by
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let D := {g : MatrixCoordinates (Fin n)→ℝ | ∃ i,
    δ < |plantedInteraction j (goeMatrix (j/(n:ℝ)) g) i i|}
  have hs : erasedPlantedRootBad n j A (K-δ) ε (c/2) (ρ/2) t ⊆
      plantedRootBad n j A K ε c ρ t ∪ (D ×ˢ (Set.univ : Set (Fin n→ℝ))) := by
    intro p hp
    by_cases hd : p.1∈D
    · exact Or.inr ⟨hd,mem_univ _⟩
    · apply Or.inl
      exact erased_planted_witness hA hδ.le hδρ hδc t p.1 p.2
        (fun i=>le_of_not_gt (fun hi=>hd ⟨i,hi⟩)) hp.1 hp.2
  have hD : (μ.prod ν).real (D ×ˢ (Set.univ : Set (Fin n→ℝ))) ≤
      2*(n:ℝ)*exp (-(δ^2/(32*j))*(n:ℝ)) := by
    rw [measureReal_prod_prod]
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one]
    exact shifted_goe_diagonal_tail hj hδ hn hmean
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add hp hD))

theorem zero_diagonal_fixed_time_root_stability {j T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hT : 0 < T) :
    ∃ A K ε c ρ a : ℝ, 1 < A ∧ 2*sqrt j < K ∧ sqrt j*A < 1 ∧
      0 < ε ∧ 0 < c ∧ 0 < ρ ∧ 0 < a ∧ ∃ N : ℕ, 0 < N ∧
      ∀ n ≥ N, ∀ t∈Icc 0 T,
      ((gaussianCoordinates (MatrixCoordinates (Fin n))).prod
       (Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))).real
        (erasedPlantedRootBad n j A K ε c ρ t) ≤ exp (-a*(n:ℝ)) := by
  obtain ⟨A,K,ε,c,ρ,a,hA,hK,hsub,hε,hc,hρ,ha,N,hN,hp⟩ :=
    planted_fixed_time_root_stability hj hj1 hT
  let δ := min ((K-2*sqrt j)/2) (min (ρ/2) (c/(2*A)))
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hδ : 0 < δ := lt_min (by linarith) (lt_min (half_pos hρ) (by positivity))
  have hδK : δ ≤ (K-2*sqrt j)/2 := min_le_left _ _
  have hδρ : δ ≤ ρ/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδc' : δ ≤ c/(2*A) := (min_le_right _ _).trans (min_le_right _ _)
  have hδc : A*δ ≤ c/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*A)).mp hδc'
    nlinarith
  let b := δ^2/(32*j)
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨Nd,hNd⟩ := absorb_linear_exponential hb
  obtain ⟨Nm,hNm⟩ := exists_nat_ge (2*j/δ)
  obtain ⟨r,hr,Nr,hNr⟩ := two_exponential_tails ha (half_pos hb)
  refine ⟨A,K-δ,ε,c/2,ρ/2,r,hA,by linarith,hsub,hε,half_pos hc,half_pos hρ,hr,
    max N (max Nd (max Nm Nr)),hN.trans_le (le_max_left _ _),?_⟩
  intro n hn t ht
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnD : Nd ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnM : Nm ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hnR : Nr ≤ n := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hn0 : 0 < n := hN.trans_le hnN
  have hmean : j/(n:ℝ) ≤ δ/2 := by
    have hh := (div_le_iff₀ hδ).mp (hNm.trans (Nat.cast_le.mpr hnM))
    apply (div_le_iff₀ (Nat.cast_pos.mpr hn0)).mpr
    nlinarith
  have hh := erased_planted_probability hj hA0.le hδ hn0 hδρ hδc hmean (hp n hnN t ht)
  apply hh.trans
  apply (add_le_add_right (hNd n hnD) _).trans
  exact (by nlinarith only [exp_pos (-a*(n:ℝ))] :
    exp (-a*(n:ℝ))+exp (-(b/2)*(n:ℝ)) ≤
      4*exp (-a*(n:ℝ))+exp (-(b/2)*(n:ℝ))).trans (hNr n hnR)
end SKGap.ObservationBridge

end
end

end OAI
