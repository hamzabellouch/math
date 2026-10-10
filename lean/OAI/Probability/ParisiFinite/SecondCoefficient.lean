import Mathlib
import OAI.Probability.ParisiFinite.Joint

namespace OAI

/-! Second Coefficient. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
namespace QuantumCLT
open scoped Topology
open Filter
 

def secondCoefficient {ι : Type*} (q : ι → ι → ℂ) : List ι → ℂ
  | [] => 0
  | i::l => (2:ℂ)⁻¹*q i i+secondCoefficient q l+(l.map (q i)).sum

theorem second_matrixElement {ι A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (l : List ι) (X : ι → A) (φ : A →L[ℂ] ℂ) :
    φ (second (l.map X))=secondCoefficient (fun i j => φ (X i*X j)) l := by
  induction l with
  | nil => simp [second,secondCoefficient]
  | cons i l ih =>
    simp only [List.map_cons,second,secondCoefficient,map_add,map_smul,smul_eq_mul,ih]
    congr 1
    · rw [pow_two]
    · have hsum : X i*(l.map X).sum=(l.map (fun j => X i*X j)).sum := by
        clear ih
        induction l with
        | nil => simp
        | cons j l ih => simp only [List.map_cons,List.sum_cons,mul_add,ih]
      rw [hsum,map_list_sum,List.map_map]
      rfl

theorem secondCoefficient_tendsto {ι : Type*} (l : List ι)
    (q : ℕ → ι → ι → ℂ) (q₀ : ι → ι → ℂ)
    (hq : ∀i ∈ l, ∀j ∈ l, Tendsto (fun n => q n i j) atTop (𝓝 (q₀ i j))) :
    Tendsto (fun n => secondCoefficient (q n) l) atTop (𝓝 (secondCoefficient q₀ l)) := by
  induction l with
  | nil => exact tendsto_const_nhds
  | cons i l ih =>
    apply Tendsto.add
    · apply Tendsto.add
      · exact (hq i (by simp) i (by simp)).const_mul _
      · exact ih (fun a ha b hb => hq a (by simp [ha]) b (by simp [hb]))
    · exact tendsto_list_sum l (fun j hj => hq i (by simp) j (by simp [hj]))

 

theorem moving_generators_gram_limit
    {ι : Type*} (A : ℕ → Type*) [∀n, NormedRing (A n)] [∀n, NormedAlgebra ℂ (A n)]
    [∀n, NormOneClass (A n)] [∀n, CompleteSpace (A n)]
    (l : List ι) (X : ∀n, ι → A n) (φ : ∀n, A n →L[ℂ] ℂ)
    (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hX : ∀n i, i ∈ l → ‖X n i‖ ≤ L) (hφ : ∀n, ‖φ n‖ ≤ K)
    (h1 : ∀n, φ n 1=1) (hc : ∀n, φ n (l.map (X n)).sum=0)
    (q : ι → ι → ℂ)
    (hq : ∀i ∈ l, ∀j ∈ l, Tendsto (fun n => φ n (X n i*X n j)) atTop (𝓝 (q i j))) :
    Tendsto (fun n : ℕ => (φ n (generators (l.map (X n)) (Real.sqrt (n:ℝ))⁻¹))^n)
      atTop (𝓝 (Complex.exp (secondCoefficient q l))) := by
  apply moving_generators_vacuum_limit A l X φ L K hL hK hX hφ h1 hc
  simp_rw [second_matrixElement]
  exact secondCoefficient_tendsto l _ q hq

 

theorem scalar_first_limit (g a : ℕ → ℂ) (v : ℂ)
    (ha : Tendsto a atTop (𝓝 v)) (C : ℝ)
    (hg : ∀n : ℕ, 0<n → ‖g n-((Real.sqrt (n:ℝ))⁻¹:ℂ)*a n‖ ≤ C*(n:ℝ)⁻¹) :
    Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ):ℂ)*g n) atTop (𝓝 v) := by
  have hs : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have he : Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ):ℂ)*g n-a n) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (by simpa using hs.const_mul C)
    filter_upwards [Filter.eventually_gt_atTop (0:ℕ)] with n hn
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    have hsn : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
    have hsC : (Real.sqrt (n:ℝ):ℂ) ≠ 0 := by exact_mod_cast hsn
    calc
      _ = ‖(Real.sqrt (n:ℝ):ℂ)*(g n-((Real.sqrt (n:ℝ))⁻¹:ℂ)*a n)‖ := by
        congr 1; field_simp
      _ = Real.sqrt (n:ℝ)*‖g n-((Real.sqrt (n:ℝ))⁻¹:ℂ)*a n‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (n:ℝ)*(C*(n:ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (hg n hn) (Real.sqrt_nonneg _)
      _ = C*(Real.sqrt (n:ℝ))⁻¹ := by
        nth_rw 2 [←Real.sq_sqrt hnR.le]
        field_simp
  convert he.add ha using 1 <;> simp

end QuantumCLT

namespace QuantumCLT
open scoped Topology
open Filter
 
theorem step_tendsto_one (f : ℕ → ℂ) {z : ℂ}
    (hf : Tendsto (fun n : ℕ => (n:ℂ)*(f n-1)) atTop (𝓝 z)) :
    Tendsto f atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (n:ℂ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hh := (hi.mul hf).add_const 1
  simp only [zero_mul,zero_add] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_gt_atTop (0:ℕ)] with n hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

 
theorem scalar_power_pred_limit (f b : ℕ → ℂ) (z : ℂ)
    (hb : Tendsto b atTop (𝓝 z)) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n : ℕ, 0 < n → ‖f n-1-(n:ℂ)⁻¹*b n‖ ≤ C*(Real.sqrt (n:ℝ))⁻¹^3) :
    Tendsto (fun n => f n^(n-1)) atTop (𝓝 (Complex.exp z)) := by
  have hone := step_tendsto_one f (scalar_scaled_limit f b z hb C hC hf)
  have hp := scalar_power_limit f b z hb C hC hf
  have hd := hp.div hone one_ne_zero
  simp only [div_one] at hd
  apply hd.congr'
  filter_upwards [hone.eventually_ne one_ne_zero,Filter.eventually_gt_atTop (0:ℕ)] with n hn hnpos
  simpa [div_eq_mul_inv] using (pow_sub₀ (f n) hn hnpos).symm

 

theorem scalar_inserted_limit (f b g a : ℕ → ℂ) (z v : ℂ)
    (hb : Tendsto b atTop (𝓝 z)) (ha : Tendsto a atTop (𝓝 v))
    (C D : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n : ℕ, 0 < n → ‖f n-1-(n:ℂ)⁻¹*b n‖ ≤ C*(Real.sqrt (n:ℝ))⁻¹^3)
    (hg : ∀n : ℕ, 0<n → ‖g n-((Real.sqrt (n:ℝ))⁻¹:ℂ)*a n‖ ≤ D*(n:ℝ)⁻¹) :
    Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ):ℂ)*g n*f n^(n-1))
      atTop (𝓝 (v*Complex.exp z)) :=
  (scalar_first_limit g a v ha D hg).mul (scalar_power_pred_limit f b z hb C hC hf)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A]

omit [NormOneClass A] in
 

theorem JetBound.insertion {L K : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K)
    {f : ℝ → A} {a b : A} (hf : JetBound L f a b)
    (ψ : A →L[ℂ] ℂ) (hψ : ‖ψ‖ ≤ K) (h1 : ψ 1=0)
    (r : ℝ) (hr : |r| ≤ 1) :
    ‖ψ (f r)-(r:ℂ)*ψ a‖ ≤ 2*K*L*|r|^2 := by
  have hpow : |r|^3 ≤ |r|^2 := by
    nlinarith [sq_nonneg |r|,abs_nonneg r]
  have he : ‖f r-1-(r:ℂ) • a‖ ≤ 2*L*|r|^2 := by
    calc
      _ ≤ ‖f r-1-(r:ℂ) • a-((r:ℂ)^2) • b‖+‖((r:ℂ)^2) • b‖ := norm_le_norm_sub_add _ _
      _ ≤ L*|r|^3+|r|^2*L := by
        apply add_le_add (hf.2.2 r hr)
        simpa [norm_smul,norm_pow] using mul_le_mul_of_nonneg_left hf.2.1 (sq_nonneg |r|)
      _ ≤ 2*L*|r|^2 := by nlinarith [mul_le_mul_of_nonneg_left hpow hL]
  calc
    _ = ‖ψ (f r-1-(r:ℂ) • a)‖ := by simp [h1]
    _ ≤ ‖ψ‖*‖f r-1-(r:ℂ) • a‖ := ψ.le_opNorm _
    _ ≤ K*(2*L*|r|^2) := mul_le_mul hψ he (norm_nonneg _) hK
    _ = _ := by ring

end QuantumCLT

namespace QuantumCLT
open scoped Topology
open Filter
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]

 
theorem JetBound.vacuum {L K : ℝ} (hK : 0 ≤ K)
    {f : ℝ → A} {a b : A} (hf : JetBound L f a b)
    (φ : A →L[ℂ] ℂ) (hφ : ‖φ‖ ≤ K) (h1 : φ 1=1) (hc : φ a=0)
    (r : ℝ) (hr : |r| ≤ 1) :
    ‖φ (f r)-1-(r:ℂ)^2*φ b‖ ≤ K*L*|r|^3 := by
  calc
    _ = ‖φ (f r-1-(r:ℂ) • a-((r:ℂ)^2) • b)‖ := by simp [h1,hc]
    _ ≤ ‖φ‖*‖f r-1-(r:ℂ) • a-((r:ℂ)^2) • b‖ := φ.le_opNorm _
    _ ≤ K*(L*|r|^3) := mul_le_mul hφ (hf.2.2 r hr) (norm_nonneg _) hK
    _ = _ := by ring

theorem sqrt_inverse_bound (n : ℕ) (hn : 0<n) : |(Real.sqrt (n:ℝ))⁻¹| ≤ 1 := by
  rw [abs_of_nonneg (by positivity)]
  apply inv_le_one_of_one_le₀
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  have : (1:ℝ) ≤ n := by exact_mod_cast hn
  simpa using this

theorem sqrt_inverse_sq (n : ℕ) : (((Real.sqrt (n:ℝ))⁻¹:ℝ):ℂ)^2=(n:ℂ)⁻¹ := by
  rw [←Complex.ofReal_pow,inv_pow,Real.sq_sqrt (by positivity),Complex.ofReal_inv,Complex.ofReal_natCast]

 

theorem moving_generators_inserted_limit
    {ι : Type*} (A : ℕ → Type*) [∀n, NormedRing (A n)] [∀n, NormedAlgebra ℂ (A n)]
    [∀n, NormOneClass (A n)] [∀n, CompleteSpace (A n)]
    (l : List ι) (X : ∀n, ι → A n) (φ ψ : ∀n, A n →L[ℂ] ℂ)
    (L K M : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hX : ∀n i, i ∈ l → ‖X n i‖ ≤ L) (hφ : ∀n, ‖φ n‖ ≤ K)
    (hψ : ∀n, ‖ψ n‖ ≤ M) (h1 : ∀n, φ n 1=1) (h0 : ∀n, ψ n 1=0)
    (hc : ∀n, φ n (l.map (X n)).sum=0)
    {z v : ℂ} (hz : Tendsto (fun n => φ n (second (l.map (X n)))) atTop (𝓝 z))
    (hv : Tendsto (fun n => ψ n (l.map (X n)).sum) atTop (𝓝 v)) :
    Tendsto (fun n : ℕ => (Real.sqrt (n:ℝ):ℂ)*
      ψ n (generators (l.map (X n)) (Real.sqrt (n:ℝ))⁻¹)*
      (φ n (generators (l.map (X n)) (Real.sqrt (n:ℝ))⁻¹))^(n-1))
      atTop (𝓝 (v*Complex.exp z)) := by
  have hj (n : ℕ) := generators_jetBound (l.map (X n)) hL (by
    intro Y hY
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hY
    exact hX n i hi)
  simp only [List.length_map] at hj
  apply scalar_inserted_limit _ (fun n => φ n (second (l.map (X n)))) _
    (fun n => ψ n (l.map (X n)).sum) z v hz hv
    (K*orderedBound L l.length) (2*M*orderedBound L l.length)
    (mul_nonneg hK (orderedBound_nonneg hL _))
  · intro n hn
    have hh := (hj n).vacuum hK (φ n) (hφ n) (h1 n) (hc n)
      (Real.sqrt (n:ℝ))⁻¹ (sqrt_inverse_bound n hn)
    simpa only [sqrt_inverse_sq,abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (n:ℝ))⁻¹)] using hh
  · intro n hn
    have hh := (hj n).insertion (orderedBound_nonneg hL _) hM (ψ n) (hψ n) (h0 n)
      (Real.sqrt (n:ℝ))⁻¹ (sqrt_inverse_bound n hn)
    rw [abs_of_nonneg (by positivity),inv_pow,Real.sq_sqrt (by positivity)] at hh
    simpa only [Complex.ofReal_inv] using hh

end QuantumCLT

namespace QuantumCLT
open scoped InnerProductSpace Topology
open Filter
open CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

 
def weylProduct : List E → (Space E →L[ℂ] Space E)
  | [] => ContinuousLinearMap.id ℂ (Space E)
  | d::ds => (W d).comp (weylProduct ds)

theorem secondCoefficient_gram_cons (d : E) (ds : List E) :
    secondCoefficient (fun x y : E => -⟪x,y⟫_ℂ) (d::ds)=
      (2:ℂ)⁻¹*(-⟪d,d⟫_ℂ)+secondCoefficient (fun x y : E => -⟪x,y⟫_ℂ) ds-
      ⟪d,ds.sum⟫_ℂ := by
  simp only [secondCoefficient]
  suffices (ds.map (fun y => -⟪d,y⟫_ℂ)).sum= -⟪d,ds.sum⟫_ℂ by rw [this]; rfl
  induction ds with
  | nil => simp
  | cons x ds ih => simp [ih,inner_add_right,add_comm]

theorem gram_exponent (d e : E) (c : ℂ) :
    c+Complex.ofReal (‖e‖^2/2)+Complex.ofReal (-(⟪d,e⟫_ℂ).im)*Complex.I =
      (2:ℂ)⁻¹*(-⟪d,d⟫_ℂ)+c-⟪d,e⟫_ℂ+Complex.ofReal (‖d+e‖^2/2) := by
  rw [inner_self_eq_norm_sq_to_K,norm_add_sq (𝕜 := ℂ)]
  apply Complex.ext <;> simp <;> ring

 

theorem weylProduct_coherent_zero (ds : List E) :
    weylProduct ds (coherent (0:E))=
      Complex.exp (secondCoefficient (fun x y : E => -⟪x,y⟫_ℂ) ds+
        Complex.ofReal (‖ds.sum‖^2/2)) • coherent ds.sum := by
  induction ds with
  | nil => simp [weylProduct,secondCoefficient]
  | cons d ds ih =>
    simp only [weylProduct,ContinuousLinearMap.comp_apply,ih,map_smul,W_coherent,smul_smul,
      List.sum_cons,secondCoefficient_gram_cons]
    unfold phase
    rw [←Complex.exp_add,gram_exponent]

theorem weylProduct_vacuum (ds : List E) :
    ⟪coherent (0:E),weylProduct ds (coherent (0:E))⟫_ℂ=
      Complex.exp (secondCoefficient (fun x y : E => -⟪x,y⟫_ℂ) ds) := by
  rw [weylProduct_coherent_zero,inner_smul_right,inner_coherent]
  simp only [kernel,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),neg_zero,zero_div,
    Complex.ofReal_zero,inner_zero_left,zero_add]
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem secondCoefficient_map {ι : Type*} (l : List ι) (d : ι → E) :
    secondCoefficient (fun x y : E => -⟪x,y⟫_ℂ) (l.map d)=
      secondCoefficient (fun i j => -⟪d i,d j⟫_ℂ) l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.map_cons,secondCoefficient,ih,List.map_map]; rfl

 

theorem moving_generators_weyl_limit
    {ι : Type*} (A : ℕ → Type*) [∀n, NormedRing (A n)] [∀n, NormedAlgebra ℂ (A n)]
    [∀n, NormOneClass (A n)] [∀n, CompleteSpace (A n)]
    (l : List ι) (X : ∀n, ι → A n) (φ : ∀n, A n →L[ℂ] ℂ) (d : ι → E)
    (L K : ℝ) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hX : ∀n i, i ∈ l → ‖X n i‖ ≤ L) (hφ : ∀n, ‖φ n‖ ≤ K)
    (h1 : ∀n, φ n 1=1) (hc : ∀n, φ n (l.map (X n)).sum=0)
    (hq : ∀i ∈ l, ∀j ∈ l,
      Tendsto (fun n => φ n (X n i*X n j)) atTop (𝓝 (-⟪d i,d j⟫_ℂ))) :
    Tendsto (fun n : ℕ => (φ n (generators (l.map (X n)) (Real.sqrt (n:ℝ))⁻¹))^n)
      atTop (𝓝 ⟪coherent (0:E),weylProduct (l.map d) (coherent (0:E))⟫_ℂ) := by
  rw [weylProduct_vacuum,secondCoefficient_map]
  exact moving_generators_gram_limit A l X φ L K hL hK hX hφ h1 hc _ hq

end QuantumCLT

open scoped BigOperators InnerProductSpace
namespace FiniteTensor
open Matrix
variable {ι : Type*} [Fintype ι]
 
def power (D : ℕ) (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (Fin D → ι) :=
  WithLp.toLp 2 (fun σ => ∏i, v (σ i))

omit [Fintype ι] in
@[simp] theorem power_apply (D : ℕ) (v : EuclideanSpace ℂ ι) (σ : Fin D → ι) :
    power D v σ=∏i, v (σ i) := rfl

 

theorem inner_power (D : ℕ) (v w : EuclideanSpace ℂ ι) :
    ⟪power D v,power D w⟫_ℂ=⟪v,w⟫_ℂ^D := by
  classical
  simp only [PiLp.inner_apply,RCLike.inner_apply]
  change (∑σ : Fin D → ι, (∏i, w (σ i))*starRingEnd ℂ (∏i, v (σ i)))=
    (∑j, w j*starRingEnd ℂ (v j))^D
  simp_rw [map_prod,←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun (_ : Fin D) (j : ι) => w j*starRingEnd ℂ (v j))]
  simp

 
def matrixPower (D : ℕ) (M : Matrix ι ι ℂ) : Matrix (Fin D → ι) (Fin D → ι) ℂ :=
  fun σ τ => ∏i, M (σ i) (τ i)

theorem matrixPower_mulVec (D : ℕ) (M : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    matrixPower D M *ᵥ (power D v).ofLp=
      (power D (WithLp.toLp 2 (M *ᵥ v.ofLp))).ofLp := by
  classical
  funext σ
  change (∑τ : Fin D → ι, (∏i, M (σ i) (τ i))*(∏i, v (τ i)))=
    ∏i, ∑j, M (σ i) j*v j
  simp_rw [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => M (σ i) j*v j)).symm

variable [DecidableEq ι]
 

def operatorPower (D : ℕ) (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Fin D → ι) →L[ℂ] EuclideanSpace ℂ (Fin D → ι) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin D → ι))
    (matrixPower D ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm T))

theorem operatorPower_apply (D : ℕ) (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (v : EuclideanSpace ℂ ι) : operatorPower D T (power D v)=power D (T v) := by
  apply WithLp.ofLp_injective
  rw [operatorPower,Matrix.ofLp_toEuclideanCLM,matrixPower_mulVec]
  congr 2
  have hh := congrArg (fun S : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι => S v)
    (Matrix.toEuclideanCLM.apply_symm_apply T)
  simpa only [←Matrix.toEuclideanCLM_toLp,WithLp.toLp_ofLp] using hh

 
theorem inner_operatorPower (D : ℕ) (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (v w : EuclideanSpace ℂ ι) :
    ⟪power D v,operatorPower D T (power D w)⟫_ℂ=⟪v,T w⟫_ℂ^D := by
  rw [operatorPower_apply,inner_power]

end FiniteTensor

namespace QuantumCLT
open scoped InnerProductSpace Topology
open ContinuousLinearMap Filter InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

 
def vacuumFunctional (Ω : E) : (E →L[ℂ] E) →L[ℂ] ℂ :=
  (innerSL ℂ Ω).comp (ContinuousLinearMap.apply ℂ E Ω)

@[simp] theorem vacuumFunctional_apply (Ω : E) (T : E →L[ℂ] E) :
    vacuumFunctional Ω T=⟪Ω,T Ω⟫_ℂ := rfl

theorem vacuumFunctional_norm (Ω : E) : ‖vacuumFunctional Ω‖ ≤ ‖Ω‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro T
  calc
    _ ≤ ‖Ω‖*‖T Ω‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖*(‖T‖*‖Ω‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
    _ = ‖Ω‖^2*‖T‖ := by ring

variable [Nontrivial E]

 

def testGate (Ω x : E) (r : ℝ) : E →L[ℂ] E :=
  1+(r:ℂ) • rankOne ℂ x Ω

omit [Nontrivial E] in
theorem testGate_jetBound (Ω x : E) (hΩ : ‖Ω‖=1) {R : ℝ} (hR : 0 ≤ R)
    (hx : ‖x‖ ≤ R) : JetBound R (testGate Ω x) (rankOne ℂ x Ω) 0 := by
  refine ⟨by simpa [hΩ] using hx,by simpa using hR,?_⟩
  intro r hr
  simp only [testGate,smul_zero,add_sub_cancel_left,sub_self,norm_zero]
  positivity

 
def testedGate (Ω x z : E) (f : ℝ → E →L[ℂ] E) (r : ℝ) : E →L[ℂ] E :=
  testGate z Ω r*f r*testGate Ω x r

omit [Nontrivial E] in
theorem testedGate_pairing (Ω x z : E) (hΩ : ‖Ω‖=1)
    (f : ℝ → E →L[ℂ] E) (r : ℝ) :
    vacuumFunctional Ω (testedGate Ω x z f r)=
      ⟪Ω+(r:ℂ) • z, f r (Ω+(r:ℂ) • x)⟫_ℂ := by
  have hΩi : ⟪Ω,Ω⟫_ℂ=1 := by rw [inner_self_eq_norm_sq_to_K,hΩ]; norm_num
  simp only [vacuumFunctional_apply,testedGate,testGate,mul_apply_eq_comp,add_apply,one_apply_eq_self,
    smul_apply,rankOne_apply,hΩi,one_smul]
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,hΩi,
    map_add,map_smul,Complex.conj_ofReal, mul_one]
  ring

 
def testedBound (L R : ℝ) : ℝ :=
  (R+L+8*R*L)+R+8*(R+L+8*R*L)*R

theorem testedBound_nonneg {L R : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) :
    0 ≤ testedBound L R := by unfold testedBound; positivity

theorem testedGate_jetBound (Ω x z : E) (hΩ : ‖Ω‖=1)
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R)
    {f : ℝ → E →L[ℂ] E} {a b : E →L[ℂ] E} (hf : JetBound L f a b) :
    JetBound (testedBound L R) (testedGate Ω x z f)
      (rankOne ℂ Ω z+a+rankOne ℂ x Ω)
      (b+rankOne ℂ Ω z*a+(rankOne ℂ Ω z+a)*rankOne ℂ x Ω) := by
  have hzj : JetBound R (testGate z Ω) (rankOne ℂ Ω z) 0 := by
    refine ⟨by simpa [hΩ] using hz,by simpa using hR,?_⟩
    intro r hr
    simp only [testGate,smul_zero,add_sub_cancel_left,sub_self,norm_zero]
    positivity
  have hleft := hzj.mul hR hL hf
  have hh := hleft.mul (by positivity : 0 ≤ R+L+8*R*L) hR (testGate_jetBound Ω x hΩ hR hx)
  have he : testedGate Ω x z f=(fun r => testGate z Ω r*f r*testGate Ω x r) := rfl
  rw [he]
  simpa only [zero_add,add_zero,testedBound] using hh

omit [Nontrivial E] in
theorem testedGate_first (Ω x z : E) (hΩ : ‖Ω‖=1) (a : E →L[ℂ] E)
    (hx : ⟪Ω,x⟫_ℂ=0) (hz : ⟪z,Ω⟫_ℂ=0) (ha : ⟪Ω,a Ω⟫_ℂ=0) :
    vacuumFunctional Ω (rankOne ℂ Ω z+a+rankOne ℂ x Ω)=0 := by
  have hΩi : ⟪Ω,Ω⟫_ℂ=1 := by rw [inner_self_eq_norm_sq_to_K,hΩ]; norm_num
  simp [vacuumFunctional_apply,hx,hz,ha]

omit [Nontrivial E] in
theorem testedGate_second (Ω x z : E) (hΩ : ‖Ω‖=1) (a b : E →L[ℂ] E) :
    vacuumFunctional Ω (b+rankOne ℂ Ω z*a+(rankOne ℂ Ω z+a)*rankOne ℂ x Ω)=
      ⟪Ω,b Ω⟫_ℂ+⟪z,a Ω⟫_ℂ+⟪z,x⟫_ℂ+⟪Ω,a x⟫_ℂ := by
  have hΩi : ⟪Ω,Ω⟫_ℂ=1 := by rw [inner_self_eq_norm_sq_to_K,hΩ]; norm_num
  simp only [vacuumFunctional_apply,add_apply,mul_apply_eq_comp,rankOne_apply,hΩi,one_smul,
    inner_add_right,inner_smul_right,mul_one]
  ring

 

theorem tested_pairing_bound (Ω x z : E) (hΩ : ‖Ω‖=1)
    {R L : ℝ} (hR : 0 ≤ R) (hL : 0 ≤ L) (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R)
    {f : ℝ → E →L[ℂ] E} {a b : E →L[ℂ] E} (hf : JetBound L f a b)
    (hxc : ⟪Ω,x⟫_ℂ=0) (hzc : ⟪z,Ω⟫_ℂ=0) (ha : ⟪Ω,a Ω⟫_ℂ=0)
    (r : ℝ) (hr : |r| ≤ 1) :
    ‖⟪Ω+(r:ℂ) • z, f r (Ω+(r:ℂ) • x)⟫_ℂ-1-
      (r:ℂ)^2*(⟪Ω,b Ω⟫_ℂ+⟪z,a Ω⟫_ℂ+⟪z,x⟫_ℂ+⟪Ω,a x⟫_ℂ)‖ ≤
      testedBound L R*|r|^3 := by
  have hj := testedGate_jetBound Ω x z hΩ hR hL hx hz hf
  have hc := testedGate_first Ω x z hΩ a hxc hzc ha
  have hnorm : ‖vacuumFunctional Ω‖ ≤ 1 := by simpa [hΩ] using vacuumFunctional_norm Ω
  have h1 : vacuumFunctional Ω 1=1 := by
    change ⟪Ω,Ω⟫_ℂ=1
    rw [inner_self_eq_norm_sq_to_K,hΩ]
    norm_num
  have hh := hj.vacuum (by norm_num : (0:ℝ) ≤ 1) (vacuumFunctional Ω) hnorm h1 hc r hr
  simpa only [testedGate_pairing Ω x z hΩ,testedGate_second Ω x z hΩ,one_mul] using hh

 

theorem moving_tested_limit
    (E : ℕ → Type*) [∀n, NormedAddCommGroup (E n)] [∀n, InnerProductSpace ℂ (E n)]
    [∀n, Nontrivial (E n)]
    (Ω x z : ∀n, E n) (f : ∀n, ℝ → E n →L[ℂ] E n) (a b : ∀n, E n →L[ℂ] E n)
    (R L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hΩ : ∀n, ‖Ω n‖=1) (hx : ∀n, ‖x n‖ ≤ R) (hz : ∀n, ‖z n‖ ≤ R)
    (hf : ∀n, JetBound L (f n) (a n) (b n))
    (hxc : ∀n, ⟪Ω n,x n⟫_ℂ=0) (hzc : ∀n, ⟪z n,Ω n⟫_ℂ=0)
    (ha : ∀n, ⟪Ω n,a n (Ω n)⟫_ℂ=0) {c : ℂ}
    (hc : Tendsto (fun n => ⟪Ω n,b n (Ω n)⟫_ℂ+⟪z n,a n (Ω n)⟫_ℂ+
      ⟪z n,x n⟫_ℂ+⟪Ω n,a n (x n)⟫_ℂ) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ =>
      ⟪Ω n+(((Real.sqrt (n:ℝ))⁻¹:ℝ):ℂ) • z n,
        f n (Real.sqrt (n:ℝ))⁻¹ (Ω n+(((Real.sqrt (n:ℝ))⁻¹:ℝ):ℂ) • x n)⟫_ℂ^n)
      atTop (𝓝 (Complex.exp c)) := by
  apply scalar_power_limit _ _ c hc (testedBound L R) (testedBound_nonneg hL hR)
  intro n hn
  have hh := tested_pairing_bound (Ω n) (x n) (z n) (hΩ n) hR hL (hx n) (hz n)
    (hf n) (hxc n) (hzc n) (ha n) (Real.sqrt (n:ℝ))⁻¹ (sqrt_inverse_bound n hn)
  simpa only [sqrt_inverse_sq,abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (n:ℝ))⁻¹)] using hh

end QuantumCLT

namespace FiniteTensor
open scoped InnerProductSpace Topology
open Filter QuantumCLT

 

def exponentialVector {ι : Type*} [Fintype ι] (D : ℕ)
    (Ω x : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (Fin D → ι) :=
  power D (Ω+(((Real.sqrt (D:ℝ))⁻¹:ℝ):ℂ) • x)

 

theorem moving_tensor_pairing_limit
    (ι : ℕ → Type*) [∀n, Fintype (ι n)] [∀n, DecidableEq (ι n)] [∀n, Nonempty (ι n)]
    (Ω x z : ∀n, EuclideanSpace ℂ (ι n))
    (f : ∀n, ℝ → EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    (a b : ∀n, EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))
    (R L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hΩ : ∀n, ‖Ω n‖=1) (hx : ∀n, ‖x n‖ ≤ R) (hz : ∀n, ‖z n‖ ≤ R)
    (hf : ∀n, JetBound L (f n) (a n) (b n))
    (hxc : ∀n, ⟪Ω n,x n⟫_ℂ=0) (hzc : ∀n, ⟪z n,Ω n⟫_ℂ=0)
    (ha : ∀n, ⟪Ω n,a n (Ω n)⟫_ℂ=0) {c : ℂ}
    (hc : Tendsto (fun n => ⟪Ω n,b n (Ω n)⟫_ℂ+⟪z n,a n (Ω n)⟫_ℂ+
      ⟪z n,x n⟫_ℂ+⟪Ω n,a n (x n)⟫_ℂ) atTop (𝓝 c)) :
    Tendsto (fun n => ⟪exponentialVector n (Ω n) (z n),
      operatorPower n (f n (Real.sqrt (n:ℝ))⁻¹) (exponentialVector n (Ω n) (x n))⟫_ℂ)
      atTop (𝓝 (Complex.exp c)) := by
  simpa only [exponentialVector,inner_operatorPower] using
    moving_tested_limit (fun n => EuclideanSpace ℂ (ι n)) Ω x z f a b R L hR hL
      hΩ hx hz hf hxc hzc ha hc

 

theorem moving_tensor_gram_limit
    (ι : ℕ → Type*) [∀n, Fintype (ι n)] [∀n, DecidableEq (ι n)] [∀n, Nonempty (ι n)]
    (Ω x z : ∀n, EuclideanSpace ℂ (ι n))
    (R : ℝ) (hR : 0 ≤ R) (hΩ : ∀n, ‖Ω n‖=1)
    (hx : ∀n, ‖x n‖ ≤ R) (hz : ∀n, ‖z n‖ ≤ R)
    (hxc : ∀n, ⟪Ω n,x n⟫_ℂ=0) (hzc : ∀n, ⟪z n,Ω n⟫_ℂ=0) {c : ℂ}
    (hc : Tendsto (fun n => ⟪z n,x n⟫_ℂ) atTop (𝓝 c)) :
    Tendsto (fun n => ⟪exponentialVector n (Ω n) (z n),exponentialVector n (Ω n) (x n)⟫_ℂ)
      atTop (𝓝 (Complex.exp c)) := by
  have hj (n : ℕ) : JetBound 0 (fun _ : ℝ => (1 : EuclideanSpace ℂ (ι n) →L[ℂ] EuclideanSpace ℂ (ι n))) 0 0 := by
    refine ⟨by simp,by simp,?_⟩
    intro r hr
    simp
  have hh := moving_tensor_pairing_limit ι Ω x z (fun _ _ => 1) (fun _ => 0) (fun _ => 0)
    R 0 hR le_rfl hΩ hx hz hj hxc hzc (by intro n; simp)
    (by simpa using hc)
  simpa [exponentialVector,operatorPower_apply] using hh

end FiniteTensor

namespace FiniteTensor
open scoped BigOperators InnerProductSpace
open Matrix ContinuousLinearMap
variable {ι : Type*} [Fintype ι]

 
def mixedPower (D : ℕ) (v : Fin D → EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Fin D → ι) := WithLp.toLp 2 (fun σ => ∏i, v i (σ i))

omit [Fintype ι] in
@[simp] theorem mixedPower_constant (D : ℕ) (v : EuclideanSpace ℂ ι) :
    mixedPower D (fun _ => v)=power D v := rfl

theorem inner_mixedPower (D : ℕ) (v w : Fin D → EuclideanSpace ℂ ι) :
    ⟪mixedPower D v,mixedPower D w⟫_ℂ=∏i, ⟪v i,w i⟫_ℂ := by
  classical
  simp only [PiLp.inner_apply,RCLike.inner_apply]
  change (∑σ : Fin D → ι, (∏i, w i (σ i))*starRingEnd ℂ (∏i, v i (σ i)))=
    ∏i, ∑j, w i j*starRingEnd ℂ (v i j)
  simp_rw [map_prod,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => w i j*starRingEnd ℂ (v i j))).symm

def mixedMatrix (D : ℕ) (M : Fin D → Matrix ι ι ℂ) :
    Matrix (Fin D → ι) (Fin D → ι) ℂ := fun σ τ => ∏i, M i (σ i) (τ i)

theorem mixedMatrix_mulVec (D : ℕ) (M : Fin D → Matrix ι ι ℂ)
    (v : Fin D → EuclideanSpace ℂ ι) :
    mixedMatrix D M *ᵥ (mixedPower D v).ofLp=
      (mixedPower D (fun i => WithLp.toLp 2 (M i *ᵥ (v i).ofLp))).ofLp := by
  classical
  funext σ
  change (∑τ : Fin D → ι, (∏i, M i (σ i) (τ i))*(∏i, v i (τ i)))=
    ∏i, ∑j, M i (σ i) j*v i j
  simp_rw [←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i j => M i (σ i) j*v i j)).symm

variable [DecidableEq ι]
 
def mixedOperator (D : ℕ)
    (T : Fin D → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Fin D → ι) →L[ℂ] EuclideanSpace ℂ (Fin D → ι) :=
  (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin D → ι))
    (mixedMatrix D (fun i => (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm (T i)))

theorem mixedOperator_apply (D : ℕ)
    (T : Fin D → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (v : Fin D → EuclideanSpace ℂ ι) :
    mixedOperator D T (mixedPower D v)=mixedPower D (fun i => T i (v i)) := by
  apply WithLp.ofLp_injective
  rw [mixedOperator,Matrix.ofLp_toEuclideanCLM,mixedMatrix_mulVec]
  congr 2
  funext i
  have hh := congrArg (fun S : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι => S (v i))
    (Matrix.toEuclideanCLM.apply_symm_apply (T i))
  simpa only [←Matrix.toEuclideanCLM_toLp,WithLp.toLp_ofLp] using hh

theorem inner_mixedOperator (D : ℕ)
    (T : Fin D → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (v w : EuclideanSpace ℂ ι) :
    ⟪power D v,mixedOperator D T (power D w)⟫_ℂ=∏i, ⟪v,T i w⟫_ℂ := by
  change ⟪mixedPower D (fun _ => v),mixedOperator D T (mixedPower D (fun _ => w))⟫_ℂ=_
  rw [mixedOperator_apply,inner_mixedPower]

omit [Fintype ι] [DecidableEq ι] in
 theorem prod_one_marked (D : ℕ) (j : Fin D) (a b : ℂ) :
    (∏i : Fin D, if i=j then a else b)=a*b^(D-1) := by
  rw [←Finset.mul_prod_erase Finset.univ (fun i : Fin D => if i=j then a else b) (Finset.mem_univ j)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏_i ∈ Finset.univ.erase j, b := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_erase] at hi
      exact ite_eq_right hi.1
    _ = b^(D-1) := by simp

 
def insertionSum (D : ℕ) (K T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Fin D → ι) →L[ℂ] EuclideanSpace ℂ (Fin D → ι) :=
  ∑j : Fin D, mixedOperator D (fun i => if i=j then T else K)

theorem inner_insertionSum (D : ℕ)
    (K T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (v w : EuclideanSpace ℂ ι) :
    ⟪power D v,insertionSum D K T (power D w)⟫_ℂ=
      (D:ℂ)*⟪v,T w⟫_ℂ*⟪v,K w⟫_ℂ^(D-1) := by
  simp only [insertionSum,_root_.sum_apply,inner_sum,inner_mixedOperator]
  have ht (j : Fin D) :
      (∏i : Fin D, ⟪v,(if i=j then T else K) w⟫_ℂ)=⟪v,T w⟫_ℂ*⟪v,K w⟫_ℂ^(D-1) := by
    convert prod_one_marked D j ⟪v,T w⟫_ℂ ⟪v,K w⟫_ℂ using 1
    apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> rfl
  simp only [ht,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]

 
def normalizedInsertion (D : ℕ)
    (K T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ (Fin D → ι) →L[ℂ] EuclideanSpace ℂ (Fin D → ι) :=
  (((Real.sqrt (D:ℝ))⁻¹:ℝ):ℂ) • insertionSum D K T

theorem inner_normalizedInsertion (D : ℕ)
    (K T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (v w : EuclideanSpace ℂ ι) :
    ⟪power D v,normalizedInsertion D K T (power D w)⟫_ℂ=
      (Real.sqrt (D:ℝ):ℂ)*⟪v,T w⟫_ℂ*⟪v,K w⟫_ℂ^(D-1) := by
  rw [normalizedInsertion,_root_.smul_apply,inner_smul_right,inner_insertionSum]
  have hh : ((Real.sqrt (D:ℝ))⁻¹:ℝ)*(D:ℝ)=Real.sqrt (D:ℝ) := by
    have hs : Real.sqrt (D:ℝ)^2=(D:ℝ) := Real.sq_sqrt (Nat.cast_nonneg D)
    calc
      _ = ((Real.sqrt (D:ℝ))⁻¹:ℝ)*Real.sqrt (D:ℝ)^2 := by rw [hs]
      _ = _ := by
        rcases eq_or_ne (Real.sqrt (D:ℝ)) 0 with h|h
        · simp [h]
        · field_simp
  have hc : (((Real.sqrt (D:ℝ))⁻¹:ℝ):ℂ)*(D:ℂ)=(Real.sqrt (D:ℝ):ℂ) := by exact_mod_cast hh
  calc
    _ = ((((Real.sqrt (D:ℝ))⁻¹:ℝ):ℂ)*(D:ℂ))*⟪v,T w⟫_ℂ*⟪v,K w⟫_ℂ^(D-1) := by ring
    _ = _ := by rw [hc]

end FiniteTensor

namespace QuantumCLT
open scoped InnerProductSpace Topology
open ContinuousLinearMap Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
 
def markedFunctional (Ω : E) (S : E →L[ℂ] E) : (E →L[ℂ] E) →L[ℂ] ℂ :=
  (((innerSL ℂ Ω).comp S).comp (ContinuousLinearMap.apply ℂ E Ω))

@[simp] theorem markedFunctional_apply (Ω : E) (S T : E →L[ℂ] E) :
    markedFunctional Ω S T=⟪Ω,S (T Ω)⟫_ℂ := rfl

theorem markedFunctional_norm (Ω : E) (S : E →L[ℂ] E) :
    ‖markedFunctional Ω S‖ ≤ ‖Ω‖^2*‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro T
  calc
    _ ≤ ‖Ω‖*‖S (T Ω)‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ω‖*(‖S‖*‖T Ω‖) := mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖Ω‖*(‖S‖*(‖T‖*‖Ω‖)) := by gcongr; exact T.le_opNorm _
    _ = ‖Ω‖^2*‖S‖*‖T‖ := by ring
end QuantumCLT

end

end OAI
