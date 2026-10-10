import Mathlib
import OAI.Probability.SKGap.Terminal.TerminalMatrixTransfer
import OAI.Probability.SKGap.Terminal.SpinLocalField

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

lemma cardinal_small_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h z : ι→ℝ) {t a b : ℝ} (ht : 0 < t)
    (hh : ((Finset.univ.filter (fun i=>|h i| < 2*t)).card:ℝ) ≤ a)
    (hz : (∑ i,z i^2) ≤ t^2*b) :
    ((Finset.univ.filter (fun i=>|h i+z i| < t)).card:ℝ) ≤ a+b := by
  let S := Finset.univ.filter (fun i=>|h i+z i| < t)
  let B := Finset.univ.filter (fun i=>|h i| < 2*t)
  let L := Finset.univ.filter (fun i=>t < |z i|)
  have hsub : S ⊆ B ∪ L := by
    intro i hi
    have hfield : |h i+z i| < t := (Finset.mem_filter.mp hi).2
    by_cases hb : |h i| < 2*t
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have he : h i=(h i+z i)+(-z i) := by ring
      have habs := abs_add_le (h i+z i) (-z i)
      rw [← he,abs_neg] at habs
      linarith only [hfield,le_of_not_gt hb,habs]
  have hL : t^2*(L.card:ℝ) ≤ ∑ i,z i^2 := by
    calc
      _ = ∑ _i ∈ L,t^2 := by simp [mul_comm]
      _ ≤ ∑ i ∈ L,z i^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := ((Finset.mem_filter.mp hi).2 : t < |z i|)
        have hs := (sq_le_sq₀ ht.le (abs_nonneg (z i))).mpr hh.le
        simpa only [sq_abs] using hs
      _ ≤ ∑ i,z i^2 := Finset.sum_le_univ_sum_of_nonneg (fun i=>sq_nonneg (z i))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le B L)
  have hcard' : (S.card:ℝ) ≤ (B.card:ℝ)+(L.card:ℝ) := by exact_mod_cast hcard
  have hLb : (L.card:ℝ) ≤ b := by
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp (hL.trans hz)
  exact hcard'.trans (add_le_add hh hLb)

lemma coupling_spin_norm_square (g : Disorder n) {M : ℝ} (hM : 0 ≤ M)
    (hJ : ‖Matrix.of (coupling g)‖ ≤ M) (x : Spin n) :
    (∑ i,(∑ j,coupling g i j*spinValue (x j))^2) ≤ M^2*(n:ℝ) := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i=>spinValue (x i))
  let w := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (Matrix.of (coupling g)) v
  have hv : ‖v‖^2=(n:ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i,spinValue (x i)^2)=(n:ℝ)
    simp
  have hw : ‖w‖ ≤ M*‖v‖ := (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (by simpa only [Matrix.l2_opNorm_toEuclideanCLM] using hJ) (norm_nonneg v))
  have hw2 := (sq_le_sq₀ (norm_nonneg w) (mul_nonneg hM (norm_nonneg v))).mpr hw
  rw [mul_pow,hv,EuclideanSpace.real_norm_sq_eq] at hw2
  exact hw2

lemma all_configurations_small_fields (g : Disorder n) (h : Fin n→ℝ) {M t α : ℝ}
    (hM : 0 ≤ M) (ht : 0 < t) (hJ : ‖Matrix.of (coupling g)‖ ≤ M)
    (hB : ((Finset.univ.filter (fun i=>|h i| < 2*t)).card:ℝ) ≤ α*(n:ℝ)/2)
    (hsmall : M^2 ≤ t^2*α/2) :
    ∀ x : Spin n,((Finset.univ.filter (fun i=>|localField g h i x| < t)).card:ℝ) ≤ α*(n:ℝ) := by
  intro x
  have hnorm := coupling_spin_norm_square g hM hJ x
  have hnorm' : (∑ i,(∑ j,coupling g i j*spinValue (x j))^2) ≤ t^2*(α*(n:ℝ)/2) := by
    apply hnorm.trans
    have hh := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n)
    nlinarith only [hh]
  have hc := cardinal_small_sum h (fun i=>∑ j,coupling g i j*spinValue (x j)) ht hB hnorm'
  have he : α*(n:ℝ)/2+α*(n:ℝ)/2=α*(n:ℝ) := by ring
  rw [he] at hc
  exact hc
end SKGap

end
end

section
noncomputable section
namespace SKGap
open scoped RealInnerProductSpace

lemma positive_form_cauchy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hpos : ∀ v,0 ≤ ⟪v,H v⟫) (u v : E) :
    ⟪u,H v⟫^2 ≤ ⟪u,H u⟫*⟪v,H v⟫ := by
  have hh : ∀ t : ℝ,0 ≤ ⟪v,H v⟫*(t*t)+(2*⟪u,H v⟫)*t+⟪u,H u⟫ := by
    intro t
    have hp := hpos (u+t • v)
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right] at hp
    have he : ⟪v,H u⟫=⟪u,H v⟫ := (real_inner_comm (H u) v).trans (hH u v)
    rw [he] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hh
  unfold discrim at hd
  nlinarith only [hd]

lemma curvature_poincare_on_kernel_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hpos : ∀ v,0 ≤ ⟪v,H v⟫)
    {ρ : ℝ} (hρ : 0 < ρ) (hcurv : ∀ v,ρ*⟪v,H v⟫ ≤ ⟪H v,H v⟫)
    (f : E) (hf : f ∈ (LinearMap.ker H)ᗮ) :
    ρ*⟪f,f⟫ ≤ ⟪f,H f⟫ := by
  have hrange : f ∈ LinearMap.range H := by
    rwa [← hH.orthogonal_range,Submodule.orthogonal_orthogonal] at hf
  obtain ⟨g,rfl⟩ := hrange
  have hc := positive_form_cauchy H hH hpos (H g) g
  have hg := hcurv g
  have hp := hpos (H g)
  have hn : 0 ≤ ⟪H g,H g⟫ := real_inner_self_nonneg
  have hh : ρ*⟪H g,H g⟫^2 ≤ ⟪H g,H (H g)⟫*⟪H g,H g⟫ := by
    calc
      _ ≤ ρ*(⟪H g,H (H g)⟫*⟪g,H g⟫) := mul_le_mul_of_nonneg_left hc hρ.le
      _ = ⟪H g,H (H g)⟫*(ρ*⟪g,H g⟫) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg hp
  by_cases hz : ⟪H g,H g⟫=0
  · rw [hz,mul_zero];exact hp
  · have hpos' : 0 < ⟪H g,H g⟫ := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith only [hh,hpos']
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators RealInnerProductSpace
variable {n : ℕ}

lemma conditionalExpectation_add (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (f+k) x=conditionalExpectation g h i f x+conditionalExpectation g h i k x := by
  unfold conditionalExpectation
  simp only [Pi.add_apply]
  ring
lemma conditionalExpectation_smul (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (c : ℝ) (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (c • f) x=c*conditionalExpectation g h i f x := by
  unfold conditionalExpectation
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

def heatBathLinear (g : Disorder n) (h : Fin n→ℝ) : (Spin n→ℝ) →ₗ[ℝ] (Spin n→ℝ) where
  toFun := heatBathGenerator g h
  map_add' f k := by
    funext x
    simp only [heatBathGenerator,conditionalExpectation_add,Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _;ring
  map_smul' c f := by
    funext x
    simp only [heatBathGenerator,conditionalExpectation_smul,Pi.smul_apply,smul_eq_mul,
      RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _;ring

def gibbsScale (g : Disorder n) (h : Fin n→ℝ) : (Spin n→ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Spin n) where
  toFun f := WithLp.toLp 2 (fun x=>sqrt (mass g h x)*f x)
  invFun v := fun x=>v x/sqrt (mass g h x)
  left_inv f := by
    funext x
    change sqrt (mass g h x)*f x/sqrt (mass g h x)=f x
    exact mul_div_cancel_left₀ (f x) (sqrt_pos.mpr (mass_pos g h x)).ne'
  right_inv v := by
    ext x
    exact mul_div_cancel₀ (v x) (sqrt_pos.mpr (mass_pos g h x)).ne'
  map_add' f k := by ext x;simp [mul_add]
  map_smul' c f := by ext x;simp [mul_left_comm]

lemma gibbsScale_inner (g : Disorder n) (h : Fin n→ℝ) (f k : Spin n→ℝ) :
    ⟪gibbsScale g h f,gibbsScale g h k⟫=expectation g h (fun x=>f x*k x) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  unfold dotProduct expectation
  apply Finset.sum_congr rfl
  intro x _
  change sqrt (mass g h x)*k x*(sqrt (mass g h x)*f x)=mass g h x*(f x*k x)
  calc
    _ = sqrt (mass g h x)^2*(f x*k x) := by ring
    _ = _ := by rw [sq_sqrt (mass_nonneg g h x)]

lemma heatBathLinear_const (g : Disorder n) (h : Fin n→ℝ) (c : ℝ) :
    heatBathLinear g h (fun _=>c)=0 := by
  funext x
  simp only [heatBathLinear,heatBathGenerator,LinearMap.coe_mk,AddHom.coe_mk,
    conditionalExpectation_const,sub_self,Finset.sum_const_zero,Pi.zero_apply]

lemma heatBathLinear_kernel (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    heatBathLinear g h f=0 ↔ ∀ x y,f x=f y := by
  constructor
  · intro hf
    apply (dirichlet_eq_zero_iff g h f).mp
    rw [← heatBathGenerator_form]
    change expectation g h (fun x=>f x*(heatBathLinear g h f) x)=0
    rw [hf]
    simp only [Pi.zero_apply,mul_zero,expectation_const]
  · intro hf
    have he : f=(fun _=>f (fun _=>false)) := funext (fun x=>hf x (fun _=>false))
    rw [he,heatBathLinear_const]

lemma heatBath_curvature_poincare (g : Disorder n) (h : Fin n→ℝ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ f : Spin n→ℝ,ρ*dirichlet g h f ≤
      expectation g h (fun x=>heatBathGenerator g h f x^2)) (f : Spin n→ℝ) :
    ρ*variance g h f ≤ dirichlet g h f := by
  let S := gibbsScale g h
  let H : EuclideanSpace ℝ (Spin n) →ₗ[ℝ] EuclideanSpace ℝ (Spin n) :=
    S.toLinearMap ∘ₗ heatBathLinear g h ∘ₗ S.symm.toLinearMap
  have hHS (k : Spin n→ℝ) : H (S k)=S (heatBathLinear g h k) := by simp [H]
  have hH : H.IsSymmetric := by
    intro u v
    obtain ⟨u,rfl⟩ := S.surjective u
    obtain ⟨v,rfl⟩ := S.surjective v
    rw [hHS,hHS]
    exact (gibbsScale_inner g h _ _).trans ((heatBathGenerator_adjoint g h u v).trans
      (gibbsScale_inner g h _ _).symm)
  have hform (k : Spin n→ℝ) : ⟪S k,H (S k)⟫=dirichlet g h k := by
    rw [hHS,gibbsScale_inner]
    exact heatBathGenerator_form g h k
  have hpos : ∀ v,0 ≤ ⟪v,H v⟫ := by
    intro v
    obtain ⟨k,rfl⟩ := S.surjective v
    rw [hform]
    exact dirichlet_nonneg g h k
  have hcurv : ∀ v,ρ*⟪v,H v⟫ ≤ ⟪H v,H v⟫ := by
    intro v
    obtain ⟨k,rfl⟩ := S.surjective v
    rw [hform,hHS,gibbsScale_inner]
    simpa only [sq,heatBathLinear,LinearMap.coe_mk,AddHom.coe_mk] using hc k
  let f₀ := f-(fun _=>expectation g h f)
  have hm : expectation g h f₀=0 := by
    change expectation g h (fun x=>f x-expectation g h f)=0
    rw [expectation_sub,expectation_const,sub_self]
  have hker : S f₀ ∈ (LinearMap.ker H)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    obtain ⟨k,rfl⟩ := S.surjective v
    have hk : heatBathLinear g h k=0 := by
      have hh := LinearMap.mem_ker.mp hv
      rw [hHS] at hh
      exact S.injective (by simpa using hh)
    have hk' := (heatBathLinear_kernel g h k).mp hk
    have he : k=(fun _=>k (fun _=>false)) := funext (fun x=>hk' x (fun _=>false))
    rw [gibbsScale_inner,he,expectation_const_mul,hm,mul_zero]
  have hh := curvature_poincare_on_kernel_orthogonal H hH hpos hρ hcurv (S f₀) hker
  rw [gibbsScale_inner,hform] at hh
  have hd : dirichlet g h f₀=dirichlet g h f := by
    rw [← heatBathGenerator_form,← heatBathGenerator_form]
    have he : heatBathLinear g h f₀=heatBathLinear g h f := by
      simp only [f₀,map_sub,heatBathLinear_const,sub_zero]
    change expectation g h (fun x=>f₀ x*(heatBathLinear g h f₀) x)=_
    rw [he]
    have hz : expectation g h (heatBathLinear g h f)=0 := by
      change expectation g h (fun x=>∑ i,(f x-conditionalExpectation g h i f x))=0
      rw [expectation_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [expectation_sub,expectation_conditionalExpectation,sub_self]
    simp only [f₀,Pi.sub_apply,sub_mul]
    rw [expectation_sub,expectation_const_mul,hz,mul_zero,sub_zero]
    rfl
  rw [hd] at hh
  simpa only [variance,f₀,Pi.sub_apply,sq] using hh
end SKGap

end
end

end OAI
