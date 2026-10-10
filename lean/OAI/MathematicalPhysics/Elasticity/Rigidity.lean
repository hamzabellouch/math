import OAI.MathematicalPhysics.Elasticity.Holomorphy

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

def diagonalGauge (d : n → ℂ) (A : Matrix n n Smooth) : Matrix n n Smooth :=
  fun i j => ((d i)⁻¹*d j) • A i j
omit [DecidableEq n] in
lemma diagonalGauge_mul (d : n → ℂ) (hd : ∀ i,d i≠0) (A B : Matrix n n Smooth) :
    diagonalGauge d (A*B)=diagonalGauge d A*diagonalGauge d B := by
  funext i j
  simp only [diagonalGauge,Matrix.mul_apply,Finset.smul_sum,smul_mul_smul_comm]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  field_simp [hd k]
omit [Fintype n] [DecidableEq n] in
lemma diagonalGauge_sub (d : n → ℂ) (A B : Matrix n n Smooth) :
    diagonalGauge d (A-B)=diagonalGauge d A-diagonalGauge d B := by
  funext i j
  exact smul_sub _ _ _
omit [Fintype n] in
lemma diagonalGauge_one (d : n → ℂ) (hd : ∀ i,d i≠0) :
    diagonalGauge d (1 : Matrix n n Smooth)=1 := by
  funext i j
  simp only [diagonalGauge,Matrix.one_apply]
  split_ifs with h
  · subst j; simp [hd i]
  · simp only [smul_zero]
omit [Fintype n] [DecidableEq n] in
lemma matrixD_diagonalGauge (θ : Fin 3 → ℂ) (d : n → ℂ) (G : Matrix n n Smooth) :
    matrixD θ (diagonalGauge d G)=diagonalGauge d (matrixD θ G) := by
  funext i j
  exact (thetaDerivation θ).map_smul _ _
omit [Fintype n] [DecidableEq n] in
lemma matrixD_direction_smul (θ : Fin 3 → ℂ) (c : ℂ) (G : Matrix n n Smooth) :
    matrixD (c • θ) G=c • matrixD θ G := by
  funext i j
  change thetaDerivation (c • θ) (G i j)=c • thetaDerivation θ (G i j)
  simp only [thetaDerivation_apply,direction,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,mul_smul]
omit [Fintype n] [DecidableEq n] in
lemma diagonalGauge_smul (d : n → ℂ) (c : ℂ) (G : Matrix n n Smooth) :
    diagonalGauge d (c • G)=c • diagonalGauge d G := by
  funext i j
  change ((d i)⁻¹*d j) • (c • G i j)=c • (((d i)⁻¹*d j) • G i j)
  exact smul_comm _ _ _
omit [DecidableEq n] in
lemma diagonalGauge_equation (θ : Fin 3 → ℂ) (c : ℂ) (d : n → ℂ) (hd : ∀ i,d i≠0)
    (M₀ M₁ G : Matrix n n Smooth) (he : matrixD θ G=M₁*G-G*M₀) :
    matrixD (c • θ) (diagonalGauge d G)=
      (c • diagonalGauge d M₁)*diagonalGauge d G-diagonalGauge d G*(c • diagonalGauge d M₀) := by
  rw [matrixD_direction_smul,matrixD_diagonalGauge,he,diagonalGauge_sub,
    diagonalGauge_mul d hd,diagonalGauge_mul d hd,smul_sub,smul_mul_assoc,mul_smul_comm]
omit [Fintype n] in
lemma diagonalGauge_supported {K : Set X} (hK : IsClosed K) (d : n → ℂ) (hd : ∀ i,d i≠0)
    (G : Matrix n n Smooth)
    (hs : ∀ i j,tsupport ((G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K) :
    ∀ i j,tsupport ((diagonalGauge d G i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆K := by
  intro i j
  apply closure_minimal _ hK
  intro x hx
  by_contra hnx
  apply hx
  have hz := image_eq_zero_of_notMem_tsupport (fun hh => hnx (hs i j hh))
  change (G i j : X → ℂ) x-((1 : Matrix n n Smooth) i j : X → ℂ) x=0 at hz
  have he := sub_eq_zero.mp hz
  have ho := congrArg (fun A : Matrix n n Smooth => (A i j : X → ℂ) x) (diagonalGauge_one d hd)
  change ((d i)⁻¹*d j)*(G i j : X → ℂ) x-((1 : Matrix n n Smooth) i j : X → ℂ) x=0
  rw [he]
  exact sub_eq_zero.mpr ho
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
lemma direction_theta_smul (θ : Fin 3 → ℂ) (c : ℂ) (f : Smooth) :
    direction (A := Smooth) coord (c • θ) f=c • direction (A := Smooth) coord θ f := by
  simp only [direction,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,mul_smul]
lemma thetaGamma_smul (θ : Fin 3 → ℂ) (c : ℂ) (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) :
    thetaGamma (c • θ) r hr=c • thetaGamma θ r hr := by
  simp only [thetaGamma,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,mul_smul]
lemma transportT_smul (θ : Fin 3 → ℂ) (c : ℂ) (k r : Smooth)
    (hk : ∀ x,(k : X → ℂ) x≠0) (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    transportT (c • θ) k r hk hl=c • transportT θ k r hk hl := by
  simp only [transportT,direction_theta_smul,mul_smul_comm,smul_sub]
lemma transportQ_smul (θ : Fin 3 → ℂ) (c : ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    transportQ (c • θ) k r hr hk hl=c • transportQ θ k r hr hk hl := by
  funext i
  apply Subtype.ext
  funext x
  simp only [transportQ,direction_theta_smul,thetaGamma_smul,Pi.smul_apply,
    Subalgebra.coe_smul,Subalgebra.coe_sub,Subalgebra.coe_mul,Pi.sub_apply,Pi.mul_apply,smul_eq_mul]
  ring
end ElasticityAugmented
namespace ElasticityConic
open ElasticityAugmented

def chartDiagonal (z : ℂ) (i : Fin 3) : ℂ := if i=2 then 1 else z
lemma chartDiagonal_ne_zero {z : ℂ} (hz : z≠0) (i : Fin 3) : chartDiagonal z i≠0 := by
  simp only [chartDiagonal]
  split_ifs <;> first | exact one_ne_zero | exact hz
lemma chartTheta_transition {z : ℂ} (hz : z≠0) : chartTheta false z=z^2 • chartTheta true z⁻¹ := by
  ext i
  fin_cases i <;> simp [chartTheta,theta,chartZ₀,chartZ₁,smul_eq_mul] <;> field_simp

lemma chartMatrix_transition {z : ℂ} (hz : z≠0) (T : Smooth) (Q : Fin 3 → Smooth) :
    chartMatrix false z (z^2 • T) (z^2 • Q)=
      z^2 • diagonalGauge (chartDiagonal z) (chartMatrix true z⁻¹ T Q) := by
  ext i j x
  fin_cases i <;> fin_cases j <;>
    simp [chartMatrix,diagonalGauge,chartDiagonal,chartZ₀,chartZ₁,h₁,h₂,
      Fin.sum_univ_three,smul_eq_mul] <;> field_simp

lemma physical_chart_transition {z : ℂ} (hz : z≠0) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) :
    chartMatrix false z (transportT (chartTheta false z) k r hk hl) (transportQ (chartTheta false z) k r hr hk hl)=
      z^2 • diagonalGauge (chartDiagonal z)
        (chartMatrix true z⁻¹ (transportT (chartTheta true z⁻¹) k r hk hl) (transportQ (chartTheta true z⁻¹) k r hr hk hl)) := by
  rw [chartTheta_transition hz,transportT_smul,transportQ_smul]
  exact chartMatrix_transition hz _ _

/-- The projective conic transition law is forced by supported uniqueness;
comparisons constructed using unrelated weak subsequences glue exactly. -/
theorem supported_chart_glue (k r : Fin 2 → Smooth)
    (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
    (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
    {K : Set X} (hK : IsCompact K) (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
    (hs : ∀ b z i j,tsupport ((G b z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K)
    (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
      chartMatrix b z (transportT (chartTheta b z) (k 1) (r 1) (hk 1) (hl 1))
        (transportQ (chartTheta b z) (k 1) (r 1) (hr 1) (hk 1) (hl 1))*G b z-
      G b z*chartMatrix b z (transportT (chartTheta b z) (k 0) (r 0) (hk 0) (hl 0))
        (transportQ (chartTheta b z) (k 0) (r 0) (hr 0) (hk 0) (hl 0)))
    (z : ℂ) (hz : z≠0) : G false z=diagonalGauge (chartDiagonal z) (G true z⁻¹) := by
  let M := fun b z q => chartMatrix b z (transportT (chartTheta b z) (k q) (r q) (hk q) (hl q))
    (transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hl q))
  have ht (q : Fin 2) : M false z q=z^2 • diagonalGauge (chartDiagonal z) (M true z⁻¹ q) :=
    physical_chart_transition hz (k q) (r q) (hr q) (hk q) (hl q)
  have hE := diagonalGauge_equation (chartTheta true z⁻¹) (z^2) (chartDiagonal z)
    (chartDiagonal_ne_zero hz) (M true z⁻¹ 0) (M true z⁻¹ 1) (G true z⁻¹) (he true z⁻¹)
  rw [← chartTheta_transition hz,← ht 0,← ht 1] at hE
  have hS := diagonalGauge_supported hK.isClosed (chartDiagonal z) (chartDiagonal_ne_zero hz) (G true z⁻¹) (hs true z⁻¹)
  apply supported_matrix_unique (chartTheta false z) (chartTheta_null false z) (chartTheta_ne_zero false z)
    (M false z 0) (M false z 1) (G false z) (diagonalGauge (chartDiagonal z) (G true z⁻¹)) (he false z) hE
  intro i j
  have hc0 : HasCompactSupport ((G false z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hs false z i j)
  have hc1 : HasCompactSupport ((diagonalGauge (chartDiagonal z) (G true z⁻¹) i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hS i j)
  have hc := hc0.sub hc1
  have heq : (G false z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j)-
      (diagonalGauge (chartDiagonal z) (G true z⁻¹) i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j)=
      G false z i j-diagonalGauge (chartDiagonal z) (G true z⁻¹) i j := by abel
  simpa only [← Subalgebra.coe_sub,heq] using hc
end ElasticityConic

end
end
section
/-! Two-chart proof of precisely the holomorphic-conic rigidity step. The
analytic construction of the comparison from DN equality is NOT assumed in
the main target and is still missing. -/
noncomputable section
open Set Filter
open scoped BigOperators Topology Matrix
namespace ElasticityRigidity

abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

def θ (z : ℂ) : Fin 3 → ℂ := ![1 - z ^ 2, Complex.I * (1 + z ^ 2), 2 * z]

def e (i : Fin 3) : X := EuclideanSpace.single i 1

def D (z : ℂ) (f : X → ℂ) (x : X) : ℂ :=
  ∑ i, θ z i * fderiv ℝ f x (e i)

/-- Two-chart Liouville argument for degree-zero entries. -/
lemma sphere_function_constant {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : ContinuousAt g 0) (hglue : ∀ z : ℂ, z ≠ 0 → f z = g z⁻¹) :
    ∀ z, f z = f 0 := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hlim : Tendsto f (cocompact ℂ) (𝓝 (g 0)) := by
    apply (hg.tendsto.comp hi).congr'
    filter_upwards [show ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 by
      simpa only [Metric.cobounded_eq_cocompact] using Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
    exact (hglue z hz).symm
  intro z
  exact (hf.apply_eq_of_tendsto_cocompact z hlim).trans
    (hf.apply_eq_of_tendsto_cocompact 0 hlim).symm

/-- The negative-degree transition forces every holomorphic section to vanish. -/
lemma negative_section_zero {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : ContinuousAt g 0) (hglue : ∀ z : ℂ, z ≠ 0 → f z = z⁻¹ * g z⁻¹) :
    ∀ z, f z = 0 := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hlim : Tendsto f (cocompact ℂ) (𝓝 0) := by
    have hh := hi.mul (hg.tendsto.comp hi)
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [show ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 by
      simpa only [Metric.cobounded_eq_cocompact] using Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
    exact (hglue z hz).symm
  exact fun z => hf.apply_eq_of_tendsto_cocompact z hlim

/-- The exact chart transition for End(O(-1)² ⊕ O). The two spatial
coefficients are expressed in h₁(1,z),h₂(1,z) and h₁(w,1),h₂(w,1). -/
def HolomorphicComparison (G₀ Ginf : X → ℂ → Mat) : Prop :=
  (∀ x i j, Differentiable ℂ (fun z => G₀ x z i j)) ∧
  (∀ x i j, Differentiable ℂ (fun w => Ginf x w i j)) ∧
  (∀ x z, z ≠ 0 → ∀ i j,
    G₀ x z i j =
      (if i = 2 then (1 : ℂ) else z⁻¹) * Ginf x z⁻¹ i j *
      (if j = 2 then (1 : ℂ) else z))

lemma diagonal_degree_zero {G₀ Ginf : X → ℂ → Mat}
    (hG : HolomorphicComparison G₀ Ginf) (x : X) (i j : Fin 3)
    (hij : (i = 2 ↔ j = 2)) : ∀ z, G₀ x z i j = G₀ x 0 i j := by
  apply sphere_function_constant (hG.1 x i j) (hG.2.1 x i j).continuous.continuousAt
  intro z hz
  have he := hG.2.2 x z hz i j
  by_cases hi : i = 2
  · have hj := hij.mp hi
    simpa [hi, hj] using he
  · have hj : j ≠ 2 := fun hj => hi (hij.mpr hj)
    simpa [hi, hj, mul_comm, mul_left_comm, mul_assoc, hz] using he

lemma upperright_zero {G₀ Ginf : X → ℂ → Mat}
    (hG : HolomorphicComparison G₀ Ginf) (x : X) (i : Fin 3) (hi : i ≠ 2) :
    ∀ z, G₀ x z i 2 = 0 := by
  apply negative_section_zero (hG.1 x i 2) (hG.2.1 x i 2).continuous.continuousAt
  intro z hz
  simpa [hi] using hG.2.2 x z hz i 2

/-- Normal-form connection matrix on the finite chart; q is the bottom-left
row in this frame and T the original scalar coefficient. -/
def M (q : X → ℂ → Fin 2 → ℂ) (T : X → ℂ → ℂ) (x : X) (z : ℂ) : Mat :=
  !![0, 0, 1; 0, 0, z; q x z 0, q x z 1, T x z]

def Transport (G : X → ℂ → Mat)
    (q₁ q₂ : X → ℂ → Fin 2 → ℂ) (T₁ T₂ : X → ℂ → ℂ) : Prop :=
  ∀ x z i j, D z (fun y => G y z i j) x =
    (M q₂ T₂ x z * G x z - G x z * M q₁ T₁ x z) i j

lemma D_zero (z : ℂ) (x : X) : D z (fun _ => 0) x = 0 := by
  simp [D]

lemma top_blocks_scalar {G₀ Ginf : X → ℂ → Mat}
    {q₁ q₂ : X → ℂ → Fin 2 → ℂ} {T₁ T₂ : X → ℂ → ℂ}
    (hG : HolomorphicComparison G₀ Ginf) (hT : Transport G₀ q₁ q₂ T₁ T₂) :
    ∀ x z i j, i ≠ 2 → j ≠ 2 →
      G₀ x z i j = if i = j then G₀ x 0 2 2 else 0 := by
  have hu (i : Fin 3) (hi : i ≠ 2) (z : ℂ) : (fun x => G₀ x z i 2) = fun _ => 0 := by
    funext x
    exact upperright_zero hG x i hi z
  have hc (x : X) (z : ℂ) (i j : Fin 3) (hh : i = 2 ↔ j = 2) :=
    diagonal_degree_zero hG x i j hh z
  have hr0 (x : X) (z : ℂ) :
      G₀ x 0 2 2 - (G₀ x 0 0 0 + G₀ x 0 0 1 * z) = 0 := by
    have ht := hT x z 0 2
    rw [hu 0 (by decide) z, D_zero] at ht
    simp [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG x 0 (by decide) z] at ht
    rw [hc x z 2 2 Iff.rfl, hc x z 0 0 Iff.rfl,
      hc x z 0 1 (by decide)] at ht
    exact ht.symm
  have hr1 (x : X) (z : ℂ) :
      z * G₀ x 0 2 2 - (G₀ x 0 1 0 + G₀ x 0 1 1 * z) = 0 := by
    have ht := hT x z 1 2
    rw [hu 1 (by decide) z, D_zero] at ht
    simp [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG x 1 (by decide) z] at ht
    rw [hc x z 2 2 Iff.rfl, hc x z 1 0 (by decide),
      hc x z 1 1 Iff.rfl] at ht
    exact ht.symm
  intro x z i j hi hj
  have h00 : G₀ x 0 0 0 = G₀ x 0 2 2 := by
    have hh := hr0 x 0
    simp only [mul_zero, add_zero, sub_eq_zero] at hh
    exact hh.symm
  have h01 : G₀ x 0 0 1 = 0 := by linear_combination -(hr0 x 1) - h00
  have h10 : G₀ x 0 1 0 = 0 := by simpa using hr1 x 0
  have h11 : G₀ x 0 1 1 = G₀ x 0 2 2 := by linear_combination -(hr1 x 1) - h10
  have hi' : i = 0 ∨ i = 1 := by omega
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
  · simpa using (hc x z 0 0 Iff.rfl).trans h00
  · simpa using (hc x z 0 1 (by decide)).trans h01
  · simpa using (hc x z 1 0 (by decide)).trans h10
  · simpa using (hc x z 1 1 Iff.rfl).trans h11

lemma comparison_scalar_and_dir_zero {G₀ Ginf : X → ℂ → Mat}
    {q₁ q₂ : X → ℂ → Fin 2 → ℂ} {T₁ T₂ : X → ℂ → ℂ}
    (hG : HolomorphicComparison G₀ Ginf) (hT : Transport G₀ q₁ q₂ T₁ T₂) :
    (∀ x z, G₀ x z = G₀ x 0 2 2 • (1 : Mat)) ∧
      ∀ x z, D z (fun y => G₀ y 0 2 2) x = 0 := by
  let f : X → ℂ := fun y => G₀ y 0 2 2
  have heq00 (z : ℂ) : (fun y => G₀ y z 0 0) = f := by
    funext y
    exact top_blocks_scalar hG hT y z 0 0 (by decide) (by decide)
  have heq11 (z : ℂ) : (fun y => G₀ y z 1 1) = f := by
    funext y
    exact top_blocks_scalar hG hT y z 1 1 (by decide) (by decide)
  have heq01 (z : ℂ) : (fun y => G₀ y z 0 1) = fun _ => 0 := by
    funext y
    exact top_blocks_scalar hG hT y z 0 1 (by decide) (by decide)
  have h21 (x : X) (z : ℂ) : G₀ x z 2 1 = 0 := by
    have ht := hT x z 0 1
    rw [heq01 z, D_zero] at ht
    simpa [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG] using ht.symm
  have hd (x : X) (z : ℂ) : D z f x = 0 := by
    have ht := hT x z 1 1
    rw [heq11 z] at ht
    simpa [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG, h21 x z] using ht
  have h20 (x : X) (z : ℂ) : G₀ x z 2 0 = 0 := by
    have ht := hT x z 0 0
    rw [heq00 z, hd] at ht
    simpa [M, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      upperright_zero hG] using ht.symm
  refine ⟨?_, hd⟩
  intro x z
  ext i j
  by_cases hi : i = 2
  · subst i
    fin_cases j
    · simpa using h20 x z
    · simpa using h21 x z
    · simpa using diagonal_degree_zero hG x 2 2 Iff.rfl z
  · by_cases hj : j = 2
    · subst j
      simpa [Matrix.one_apply, hi] using upperright_zero hG x i hi z
    · simpa [Matrix.one_apply, smul_eq_mul, mul_ite] using
        top_blocks_scalar hG hT x z i j hi hj

lemma fderiv_zero_of_chart_dirs (f : X → ℂ) (x : X)
    (hf : ∀ z, D z f x = 0) : fderiv ℝ f x = 0 := by
  have h0 := hf 0
  have h1 := hf 1
  have hm := hf (-1)
  simp [D, θ, Fin.sum_univ_succ] at h0 h1 hm
  have h2 : fderiv ℝ f x (e 2) = 0 := by linear_combination (h1 - hm) / 4
  have hi : Complex.I * fderiv ℝ f x (e 1) = 0 := by linear_combination (h1 + hm) / 4
  have h₁ := (mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
  have h₀ : fderiv ℝ f x (e 0) = 0 := by simpa [h₁] using h0
  have hL : (fderiv ℝ f x).toLinearMap = (0 : X →ₗ[ℝ] ℂ) := by
    apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
    intro i
    fin_cases i <;> simpa [e] using (by assumption)
  exact DFunLike.coe_injective (congrArg (fun L : X →ₗ[ℝ] ℂ => (L : X → ℂ)) hL)

/-- Exact comparison rigidity in the two charts of the projective null conic.
The exterior identity assumption is used only at a single exterior point. -/
theorem comparison_identity {G₀ Ginf : X → ℂ → Mat}
    {q₁ q₂ : X → ℂ → Fin 2 → ℂ} {T₁ T₂ : X → ℂ → ℂ}
    (hG : HolomorphicComparison G₀ Ginf) (hT : Transport G₀ q₁ q₂ T₁ T₂)
    (hs : ∀ z i j, Differentiable ℝ (fun x => G₀ x z i j))
    {x₀ : X} (hext : G₀ x₀ 0 = 1) :
    (∀ x z, G₀ x z = 1) ∧ (∀ x w, Ginf x w = 1) := by
  obtain ⟨hscalar, hd⟩ := comparison_scalar_and_dir_zero hG hT
  have hf' (x : X) : fderiv ℝ (fun y => G₀ y 0 2 2) x = 0 :=
    fderiv_zero_of_chart_dirs _ x (hd x)
  have hf (x : X) : G₀ x 0 2 2 = 1 := by
    have he := is_const_of_fderiv_eq_zero (hs 0 2 2) hf' x x₀
    simpa [hext] using he
  have hzero (x : X) (z : ℂ) : G₀ x z = 1 := by simpa [hf x] using hscalar x z
  refine ⟨hzero, ?_⟩
  intro x w
  have hout (w : ℂ) (hw : w ≠ 0) (i j : Fin 3) : Ginf x w i j = (1 : Mat) i j := by
    have he := hG.2.2 x w⁻¹ (inv_ne_zero hw) i j
    rw [hzero] at he
    simp only [inv_inv] at he
    by_cases hij : i = j
    · subst j
      by_cases hi : i = 2
      · simpa [hi] using he.symm
      · calc
          Ginf x w i i = w * Ginf x w i i * w⁻¹ := by field_simp
          _ = (1 : Mat) i i := by simpa [hi] using he.symm
    · have hl : (if i = 2 then (1 : ℂ) else w) ≠ 0 := by
        by_cases hi : i = 2 <;> simp [hi, hw]
      have hr : (if j = 2 then (1 : ℂ) else w⁻¹) ≠ 0 := by
        by_cases hj : j = 2 <;> simp [hj, hw]
      have hz : (if i = 2 then (1 : ℂ) else w) * Ginf x w i j *
          (if j = 2 then (1 : ℂ) else w⁻¹) = 0 := by
        simpa [Matrix.one_apply, hij] using he.symm
      have hz' := (mul_eq_zero.mp hz).resolve_right hr
      have hz'' := (mul_eq_zero.mp hz').resolve_left hl
      simpa [Matrix.one_apply, hij] using hz''
  ext i j
  have hfun : (fun w : ℂ => Ginf x w i j) = fun _ => (1 : Mat) i j := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℂ))
      (hG.2.1 x i j).continuous continuous_const
    intro z hz
    exact hout z hz i j
  exact congrFun hfun w

/-- The comparison equation now yields the equality of connection matrices,
without any residual scalar gauge or assumed transport equality. -/
theorem connections_equal {G₀ Ginf : X → ℂ → Mat}
    {q₁ q₂ : X → ℂ → Fin 2 → ℂ} {T₁ T₂ : X → ℂ → ℂ}
    (hG : HolomorphicComparison G₀ Ginf) (hT : Transport G₀ q₁ q₂ T₁ T₂)
    (hs : ∀ z i j, Differentiable ℝ (fun x => G₀ x z i j))
    {x₀ : X} (hext : G₀ x₀ 0 = 1) :
    ∀ x z, M q₁ T₁ x z = M q₂ T₂ x z := by
  have hId := (comparison_identity hG hT hs hext).1
  have hfun (z : ℂ) (i j : Fin 3) : (fun y => G₀ y z i j) = fun _ => (1 : Mat) i j := by
    funext y
    rw [hId]
  intro x z
  ext i j
  have he := hT x z i j
  rw [hfun, hId] at he
  have hh : M q₂ T₂ x z i j = M q₁ T₁ x z i j := by
    simpa [D, sub_eq_zero] using he.symm
  exact hh.symm

end ElasticityRigidity

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

def physicalChartMatrix (b : Bool) (z : ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) : Matrix (Fin 3) (Fin 3) Smooth :=
  chartMatrix b z (transportT (chartTheta b z) k r hk hl)
    (transportQ (chartTheta b z) k r hr hk hl)

lemma physicalChartMatrix_regular (b : Bool) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (i j : Fin 3) :
    JointHolomorphic (fun y : X × ℂ => (physicalChartMatrix b y.2 k r hr hk hl i j : X → ℂ) y.1) := by
  apply chartMatrix_regular b (fun z => transportT (chartTheta b z) k r hk hl)
    (fun z => transportQ (chartTheta b z) k r hr hk hl)
  · exact transportT_regular b k r hk hl
  · exact transportQ_regular b k r hr hk hl

lemma physicalChartMatrix_eqOn (b : Bool) (z : ℂ) (k r : Fin 2 → Smooth)
    (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
    (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
    {O : Set X} (hO : IsOpen O) (hek : EqOn (k 0 : X → ℂ) (k 1) O)
    (her : EqOn (r 0 : X → ℂ) (r 1) O) {x : X} (hx : x∈O) :
    matrixEval x (physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0))=
      matrixEval x (physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1)) := by
  have hh := eqOn_transport hO (chartTheta b z) (k 0) (k 1) (r 0) (r 1)
    (hr 0) (hr 1) (hk 0) (hk 1) (hl 0) (hl 1) hek her
  ext i j
  have ht := hh.1 hx
  have hq : ∀ i,(transportQ (chartTheta b z) (k 0) (r 0) (hr 0) (hk 0) (hl 0) i : X → ℂ) x=
    (transportQ (chartTheta b z) (k 1) (r 1) (hr 1) (hk 1) (hl 1) i : X → ℂ) x := fun i => hh.2 i hx
  fin_cases i <;> fin_cases j <;> simp [physicalChartMatrix,matrixEval_apply,chartMatrix,smooth_sum_eval,ht,hq]

lemma chart_transition_scalar (z a : ℂ) (i j : Fin 3) :
    (chartDiagonal z i)⁻¹*chartDiagonal z j*a=
      (if i=2 then (1 : ℂ) else z⁻¹)*a*(if j=2 then (1 : ℂ) else z) := by
  simp only [chartDiagonal]
  split_ifs <;> ring

lemma chartTheta_smooth (b : Bool) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => chartTheta b z i) := by
  cases b <;> fin_cases i <;> dsimp [chartTheta,chartZ₀,chartZ₁,theta] <;> fun_prop

lemma chartTheta_false (z : ℂ) : chartTheta false z=ElasticityRigidity.θ z := by
  ext i
  fin_cases i <;> simp [chartTheta,chartZ₀,chartZ₁,theta,ElasticityRigidity.θ]

/-- The abstract conic rigidity calculation, separated from the lengthy
physical coefficient formulas. All analytic matching properties are supplied
below by proved supported uniqueness and regularity, not by inverse hypotheses. -/
theorem chart_comparison_trivial (T : Bool → ℂ → Fin 2 → Smooth)
    (Q : Bool → ℂ → Fin 2 → Fin 3 → Smooth)
    (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
    (hG : ∀ b i j,JointHolomorphic (fun y : X × ℂ => (G b y.2 i j : X → ℂ) y.1))
    (hglue : ∀ z : ℂ,z≠0 → G false z=diagonalGauge (chartDiagonal z) (G true z⁻¹))
    (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
      chartMatrix b z (T b z 1) (Q b z 1)*G b z-G b z*chartMatrix b z (T b z 0) (Q b z 0))
    (x₀ : X) (hbase : matrixEval x₀ (G false 0)=1) : ∀ b z,G b z=1 := by
  let M := fun b z q => chartMatrix b z (T b z q) (Q b z q)
  let F := fun b x z => matrixEval x (G b z)
  have hH : ElasticityRigidity.HolomorphicComparison (F false) (F true) := by
    refine ⟨fun x i j => (hG false i j).holo x,fun x i j => (hG true i j).holo x,?_⟩
    intro x z hz i j
    have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) Smooth => (A i j : X → ℂ) x)
      (hglue z hz)
    change (G false z i j : X → ℂ) x=((chartDiagonal z i)⁻¹*chartDiagonal z j)*(G true z⁻¹ i j : X → ℂ) x at hh
    change (G false z i j : X → ℂ) x=_
    exact hh.trans (chart_transition_scalar z ((G true z⁻¹ i j : X → ℂ) x) i j)
  let τ := fun q x z => (T false z q : X → ℂ) x
  let β := fun q x z (i : Fin 2) => (M false z q 2 i.castSucc : X → ℂ) x
  have hM (q x z) : ElasticityRigidity.M (β q) (τ q) x z=matrixEval x (M false z q) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ElasticityRigidity.M,β,τ,M,chartMatrix,chartZ₀,chartZ₁]
  have hT : ElasticityRigidity.Transport (F false) (β 0) (β 1) (τ 0) (τ 1) := by
    intro x z i j
    have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) Smooth => matrixEval x A i j) (he false z)
    rw [matrixD_eval] at hh
    simp only [map_sub,map_mul] at hh
    rw [hM,hM]
    simpa only [chartTheta_false,ElasticityRigidity.D,ElasticityRigidity.e,
      ElasticityParameter.basis,F,matrixEval_apply] using hh
  have hsp (z i j) : Differentiable ℝ (fun x => F false x z i j) :=
    (show ContDiff ℝ (⊤ : ℕ∞) (G false z i j : X → ℂ) from (G false z i j).property).differentiable (by simp)
  have hId := ElasticityRigidity.comparison_identity hH hT hsp hbase
  intro b z
  ext i j x
  have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A i j)
    (show F b x z=1 by cases b; exact hId.1 x z; exact hId.2 x z)
  change matrixEval x (G b z) i j=matrixEval x 1 i j
  rw [map_one]
  exact hh

/-- Rigidity of the genuine two-chart physical connection. The entire analytic
matching input is only separately smooth supported transport; joint smoothness,
holomorphy and transition compatibility are conclusions of the transport equations, never additional properties imposed upon CGO weak limits. -/
theorem supported_physical_holomorphic (k r : Fin 2 → Smooth)
    (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
    (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
    {K : Set X} (hK : IsCompact K) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈K,(χ : X → ℂ) x=1)
    (hexk : EqOn (k 0 : X → ℂ) (k 1) Kᶜ) (hexr : EqOn (r 0 : X → ℂ) (r 1) Kᶜ)
    (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
    (hs : ∀ b z i j,tsupport ((G b z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K)
    (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
      physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1)*G b z-
      G b z*physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)) :
    ∀ b i j,JointHolomorphic (fun y : X × ℂ => (G b y.2 i j : X → ℂ) y.1) := by
  let T := fun b z q => transportT (chartTheta b z) (k q) (r q) (hk q) (hl q)
  let Q := fun b z q => transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hl q)
  let M := fun b z q => chartMatrix b z (T b z q) (Q b z q)
  have hMr (b : Bool) (q : Fin 2) (i j : Fin 3) : JointHolomorphic (fun y : X × ℂ => (M b y.2 q i j : X → ℂ) y.1) :=
    physicalChartMatrix_regular b (k q) (r q) (hr q) (hk q) (hl q) i j
  have hMe (b z x) (hx : x∉K) : matrixEval x (M b z 0)=matrixEval x (M b z 1) :=
    physicalChartMatrix_eqOn b z k r hr hk hl hK.isClosed.isOpen_compl hexk hexr hx
  have hGr (b : Bool) := supported_matrix_holomorphic (fun i z => chartTheta b z i)
    (chartTheta_smooth b)
    (fun i => (chartTheta_regular b i).holo 0)
    (chartTheta_null b) (chartTheta_ne_zero b) (fun z => M b z 0) (fun z => M b z 1) (G b)
    (hMr b 0) (hMr b 1) hK χ hχ hχ1 (hs b) (hMe b) (he b)
  exact hGr

theorem physical_conic_connections_equal (k r : Fin 2 → Smooth)
    (hr : ∀ q x,(r q : X → ℂ) x≠0) (hk : ∀ q x,(k q : X → ℂ) x≠0)
    (hl : ∀ q x,((k q+r q*r q : Smooth) : X → ℂ) x≠0)
    {K : Set X} (hK : IsCompact K) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈K,(χ : X → ℂ) x=1) (x₀ : X) (hx₀ : x₀∉K)
    (hexk : EqOn (k 0 : X → ℂ) (k 1) Kᶜ) (hexr : EqOn (r 0 : X → ℂ) (r 1) Kᶜ)
    (G : Bool → ℂ → Matrix (Fin 3) (Fin 3) Smooth)
    (hs : ∀ b z i j,tsupport ((G b z i j-(1 : Matrix (Fin 3) (Fin 3) Smooth) i j : Smooth) : X → ℂ)⊆K)
    (he : ∀ b z,matrixD (chartTheta b z) (G b z)=
      physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1)*G b z-
      G b z*physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)) :
    ∀ b z,physicalChartMatrix b z (k 0) (r 0) (hr 0) (hk 0) (hl 0)=
      physicalChartMatrix b z (k 1) (r 1) (hr 1) (hk 1) (hl 1) := by
  let T := fun b z q => transportT (chartTheta b z) (k q) (r q) (hk q) (hl q)
  let Q := fun b z q => transportQ (chartTheta b z) (k q) (r q) (hr q) (hk q) (hl q)
  have hGr := supported_physical_holomorphic k r hr hk hl hK χ hχ hχ1 hexk hexr G hs he
  have hId : ∀ b z,G b z=1 := chart_comparison_trivial T Q G hGr
    (supported_chart_glue k r hr hk hl hK G hs he) he x₀
    (supported_matrix_eq_one (G false 0) (hs false 0) x₀ hx₀)
  intro b z
  have hh := he b z
  rw [hId b z,matrixD_one,mul_one,one_mul] at hh
  exact (sub_eq_zero.mp hh.symm).symm
end ElasticityConic

end
end
section
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityConic

/-- The two affine charts exhaust every nonzero complex characteristic direction,
up to its nonzero scalar. No arbitrary choice of a square root is needed. -/
lemma chart_covers_null (v : C3) (hv : v≠0) (hn : null v) :
    ∃ (b : Bool) (z c : ℂ), c≠0 ∧ v=c • chartTheta b z := by
  have hn' : v 0^2+v 1^2+v 2^2=0 := by
    simpa only [null,dot3,pow_two] using hn
  let a : ℂ := v 0-Complex.I*v 1
  by_cases ha : a=0
  · have hz : v 2=0 := by
      have hh : v 2^2=0 := by
        dsimp [a] at ha
        linear_combination hn'-(v 0+Complex.I*v 1)*ha-(v 1)^2*Complex.I_sq
      exact (pow_eq_zero_iff (by omega : (2 : ℕ)≠0)).mp hh
    have hn0 : v 0≠0 := by
      intro h
      have h1 : v 1=0 := by
        have hh : Complex.I*v 1=0 := by simpa [a,h] using ha
        exact (mul_eq_zero.mp hh).resolve_left Complex.I_ne_zero
      apply hv
      ext i
      fin_cases i <;> simp [h,h1,hz]
    refine ⟨true,0,-v 0,neg_ne_zero.mpr hn0,?_⟩
    ext i
    fin_cases i <;> simp [chartTheta,chartZ₀,chartZ₁,theta,smul_eq_mul,hz]
    dsimp [a] at ha
    linear_combination Complex.I*ha+(v 1)*Complex.I_sq
  · have h0 : a^2-v 2^2=2*a*v 0 := by
      dsimp [a]
      linear_combination -hn'+(v 1)^2*Complex.I_sq
    have h1 : Complex.I*(a^2+v 2^2)=2*a*v 1 := by
      dsimp [a]
      linear_combination Complex.I*hn'+(Complex.I*(v 1)^2-2*v 0*v 1)*Complex.I_sq
    refine ⟨false,v 2/a,a/2,div_ne_zero ha (by norm_num),?_⟩
    ext i
    fin_cases i <;> simp [chartTheta,chartZ₀,chartZ₁,theta,smul_eq_mul]
    · field_simp
      linear_combination -h0
    · field_simp
      linear_combination -h1
    · field_simp
end ElasticityConic

end
end
section
noncomputable section
open scoped BigOperators Matrix
namespace ElasticityConic
open ElasticityAugmented

lemma chart_bottom_equal (b : Bool) (z : ℂ) (T₀ T₁ : Smooth) (Q₀ Q₁ : Fin 3 → Smooth)
    (he : chartMatrix b z T₀ Q₀=chartMatrix b z T₁ Q₁) (x : X) :
    (T₀ : X → ℂ) x=(T₁ : X → ℂ) x ∧
    ∀ p : C3, dotProduct (chartTheta b z) p=0 →
      dotProduct (fun i => (Q₀ i : X → ℂ) x) p=dotProduct (fun i => (Q₁ i : X → ℂ) x) p := by
  have ht := congrArg (fun M : Matrix (Fin 3) (Fin 3) Smooth => (M 2 2 : X → ℂ) x) he
  have h0 : dotProduct (fun i => (Q₀ i : X → ℂ) x) (h₁ (chartZ₀ b z) (chartZ₁ b z))=
      dotProduct (fun i => (Q₁ i : X → ℂ) x) (h₁ (chartZ₀ b z) (chartZ₁ b z)) := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) Smooth => (M 2 0 : X → ℂ) x) he
    simpa [chartMatrix,smooth_sum_eval,dotProduct,mul_comm] using hh
  have h1 : dotProduct (fun i => (Q₀ i : X → ℂ) x) (h₂ (chartZ₀ b z) (chartZ₁ b z))=
      dotProduct (fun i => (Q₁ i : X → ℂ) x) (h₂ (chartZ₀ b z) (chartZ₁ b z)) := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) Smooth => (M 2 1 : X → ℂ) x) he
    simpa [chartMatrix,smooth_sum_eval,dotProduct,mul_comm] using hh
  refine ⟨ht,?_⟩
  intro p hp
  have hs := congrArg Prod.fst (chartVector_coord b z (p,0) hp)
  change _+_=p at hs
  rw [← hs,dotProduct_add,dotProduct_add,dotProduct_smul,dotProduct_smul,
    dotProduct_smul,dotProduct_smul,h0,h1]

end ElasticityConic
namespace ElasticityRecovery
open ElasticityConic
lemma T_smul (m k : X → ℝ) (x : X) (c : ℂ) (θ : C3) :
    T m k x (c • θ)=c*T m k x θ := by
  simp only [T,dir,smul_dotProduct,smul_eq_mul]
lemma Q_smul (m k : X → ℝ) (x : X) (c : ℂ) (θ : C3) :
    Q m k x (c • θ)=c • Q m k x θ := by
  exact Matrix.mulVec_smul _ _ _
end ElasticityRecovery
namespace ElasticityAugmented
open ElasticityConic
/-- Equality of the actual conic connections is precisely sufficient for the
restricted physical transports used by Lamé coefficient recovery. -/
theorem restricted_transports_of_chart_equal (m k : Fin 2 → X → ℝ)
    (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q)) (hk : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (k q))
    (hmp : ∀ q x,0 < m q x) (hkp : ∀ q x,0 < k q x)
    (he : ∀ b z,
      chartMatrix b z
        (transportT (chartTheta b z) (smoothOfReal (k 0) (hk 0)) (positiveRoot (m 0) (hm 0) (hmp 0))
          (fun x => Complex.ofReal_ne_zero.mpr (hkp 0 x).ne') (real_sum_nonzero (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0)))
        (transportQ (chartTheta b z) (smoothOfReal (k 0) (hk 0)) (positiveRoot (m 0) (hm 0) (hmp 0))
          (positiveRoot_nonzero (m 0) (hm 0) (hmp 0)) (fun x => Complex.ofReal_ne_zero.mpr (hkp 0 x).ne')
          (real_sum_nonzero (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0)))=
      chartMatrix b z
        (transportT (chartTheta b z) (smoothOfReal (k 1) (hk 1)) (positiveRoot (m 1) (hm 1) (hmp 1))
          (fun x => Complex.ofReal_ne_zero.mpr (hkp 1 x).ne') (real_sum_nonzero (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1)))
        (transportQ (chartTheta b z) (smoothOfReal (k 1) (hk 1)) (positiveRoot (m 1) (hm 1) (hmp 1))
          (positiveRoot_nonzero (m 1) (hm 1) (hmp 1)) (fun x => Complex.ofReal_ne_zero.mpr (hkp 1 x).ne')
          (real_sum_nonzero (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1)))) :
    ElasticityRecovery.EqualRestrictedTransports (m 0) (k 0) (m 1) (k 1) := by
  intro x θ hθ hn
  obtain ⟨b,z,c,hc,hθc⟩ := chart_covers_null θ hθ hn
  have hh := chart_bottom_equal b z _ _ _ _ (he b z) x
  have ht : ElasticityRecovery.T (m 0) (k 0) x (chartTheta b z)=
      ElasticityRecovery.T (m 1) (k 1) x (chartTheta b z) :=
    (transportT_real (chartTheta b z) (m 0) (k 0) (hm 0) (hk 0) (hmp 0) (hkp 0) x).symm.trans
      (hh.1.trans (transportT_real (chartTheta b z) (m 1) (k 1) (hm 1) (hk 1) (hmp 1) (hkp 1) x))
  have hq (q : Fin 2) : (fun i =>
      (transportQ (chartTheta b z) (smoothOfReal (k q) (hk q)) (positiveRoot (m q) (hm q) (hmp q))
        (positiveRoot_nonzero (m q) (hm q) (hmp q)) (fun x => Complex.ofReal_ne_zero.mpr (hkp q x).ne')
        (real_sum_nonzero (m q) (k q) (hm q) (hk q) (hmp q) (hkp q)) i : X → ℂ) x)=
      ElasticityRecovery.Q (m q) (k q) x (chartTheta b z) := by
    funext i
    exact transportQ_real (chartTheta b z) (m q) (k q) (hm q) (hk q) (hmp q) (hkp q) x i
  constructor
  · rw [hθc,ElasticityRecovery.T_smul,ElasticityRecovery.T_smul,ht]
  · intro p hp
    have hp' : dotProduct (chartTheta b z) p=0 := by
      rw [hθc,smul_dotProduct,smul_eq_mul] at hp
      exact (mul_eq_zero.mp hp).resolve_left hc
    have h := hh.2 p hp'
    rw [hq 0,hq 1] at h
    rw [hθc,ElasticityRecovery.Q_smul,ElasticityRecovery.Q_smul,smul_dotProduct,smul_dotProduct,h]
end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace Elasticity
open ElasticityAugmented ElasticityCGO ElasticityConic
open ElasticityCoeffBounds (ExteriorConstant)

lemma physicalChartMatrix_congr_k (b : Bool) (z : ℂ) (k₀ k₁ r : Smooth)
    (e : k₀=k₁) (hr : ∀ x,(r : X → ℂ) x≠0)
    (hk₀ : ∀ x,(k₀ : X → ℂ) x≠0) (hk₁ : ∀ x,(k₁ : X → ℂ) x≠0)
    (hl₀ : ∀ x,((k₀+r*r : Smooth) : X → ℂ) x≠0)
    (hl₁ : ∀ x,((k₁+r*r : Smooth) : X → ℂ) x≠0) :
    physicalChartMatrix b z k₀ r hr hk₀ hl₀ = physicalChartMatrix b z k₁ r hr hk₁ hl₁ := by
  subst k₁
  rfl

/-- The global transport-matching implication for a genuine common exterior.
Its only inverse-data hypothesis is equality of the physical DN maps. -/
theorem dn_global_coefficients_equal {Ω : Set X} (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1)) :
    lam 0=lam 1 ∧ m 0=m 1 := by
  have hK : IsCompact (closure Ω) := hOB.isCompact_closure
  obtain ⟨R,hR,hKR⟩ := hOB.closure.subset_closedBall_lt 1 (0 : X)
  have hr₀ : 1≤R := hR.le
  let kr := fun q x => lam q x+m q x
  have hks (q) : ContDiff ℝ (⊤ : ℕ∞) (kr q) := (hl q).add (hm q)
  have hkp (q x) : 0 < kr q x := by dsimp [kr]; have hh := hp q x; linarith
  let k := fun q => smoothOfReal (lam q) (hl q)+smoothOfReal (m q) (hm q)
  let r := fun q => positiveRoot (m q) (hm q) (fun x => (hp q x).1)
  have hr (q x) : (r q : X → ℂ) x≠0 := positiveRoot_nonzero (m q) (hm q) (fun x => (hp q x).1) x
  have hk (q x) : (k q : X → ℂ) x≠0 := by
    change (lam q x : ℂ)+(m q x : ℂ)≠0
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (hkp q x).ne'
  have hL (q x) : ((k q+r q*r q : Smooth) : X → ℂ) x≠0 := by
    have hrr : r q*r q=smoothOfReal (m q) (hm q) := positiveRoot_square (m q) (hm q) (fun x => (hp q x).1)
    rw [hrr]
    change (lam q x : ℂ)+(m q x : ℂ)+(m q x : ℂ)≠0
    rw [← Complex.ofReal_add,← Complex.ofReal_add]
    apply Complex.ofReal_ne_zero.mpr
    have hh := hp q x
    linarith
  choose G hs hge using (fun b z => dn_conic_comparison hΩ hOB R hr₀ hKR lam m hl hm hp hcll hclm he hDN b z hk hL)
  have hne : (closure Ω)ᶜ.Nonempty := Set.nonempty_compl.mpr hK.ne_univ
  obtain ⟨x₀,hx₀⟩ := hne
  let χ : Smooth := ⟨fiveCutoff R hr₀ 0,fiveCutoff_smooth R hr₀ 0⟩
  have hχ1 (x) (hx : x∈closure Ω) : (χ : X → ℂ) x=1 := by
    apply fiveCutoff_one R hr₀ 0
    simpa only [Fin.val_zero,Nat.cast_zero,add_zero] using
      Metric.closedBall_subset_closedBall (by linarith : R≤R+1) (hKR hx)
  have hek : EqOn (k 0 : X → ℂ) (k 1) (closure Ω)ᶜ := by
    intro x hx
    have hh := he x (fun hh => hx (subset_closure hh))
    change (lam 0 x : ℂ)+(m 0 x : ℂ)=(lam 1 x : ℂ)+(m 1 x : ℂ)
    rw [hh.1,hh.2]
  have her : EqOn (r 0 : X → ℂ) (r 1) (closure Ω)ᶜ := by
    intro x hx
    have hh := he x (fun hh => hx (subset_closure hh))
    change (Real.sqrt (m 0 x) : ℂ)=(Real.sqrt (m 1 x) : ℂ)
    rw [hh.2]
  have hM := physical_conic_connections_equal k r hr hk hL hK χ
    (fiveCutoff_compact R hr₀ 0) hχ1 x₀ hx₀ hek her G hs hge
  have ht : ElasticityRecovery.EqualRestrictedTransports (m 0) (kr 0) (m 1) (kr 1) := by
    apply restricted_transports_of_chart_equal m kr hm hks (fun q x => (hp q x).1) hkp
    intro b z
    have hEq (q : Fin 2) : smoothOfReal (kr q) (hks q)=k q :=
      (smoothOfReal_add (lam q) (m q) (hl q) (hm q)).symm
    exact (physicalChartMatrix_congr_k b z _ _ _ (hEq 0) _ _ _ _ _).trans
      ((hM b z).trans (physicalChartMatrix_congr_k b z _ _ _ (hEq 1) _ _ _ _ _).symm)
  have hmk := ElasticityRecovery.coefficients_equal_of_restricted_transports
    (hm 0) (hks 0) (hm 1) (hks 1) (fun x => (hp 0 x).1) (hkp 0)
    (fun x => (hp 1 x).1) (hkp 1) ht isClosed_closure.isOpen_compl ⟨x₀,hx₀⟩
    (fun x hx => (he x (fun hh => hx (subset_closure hh))).2)
    (fun x hx => by dsimp [kr]; rw [(he x (fun hh => hx (subset_closure hh))).1,(he x (fun hh => hx (subset_closure hh))).2])
  refine ⟨?_,hmk.1⟩
  funext x
  have hh := congrFun hmk.2 x
  have hm' := congrFun hmk.1 x
  dsimp [kr] at hh
  linarith
end Elasticity

end
end

end OAI
