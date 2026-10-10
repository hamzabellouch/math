import Mathlib
import OAI.Probability.SKGap.Localization.DiagonalHessianJoined
import OAI.Probability.SKGap.Localization.SparseCubeNet

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory Real Set
open scoped BigOperators

theorem sparse_uniform_exponential_shrink {M ζ r : ℝ} (hζ : 0 < ζ) (hr : 0 < r) :
    ∃ ε₀ : ℝ,0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
      [IsFiniteMeasure μ] (n : ℕ) (v : Fin n → ℝ) (_hv : ∀ i,v i ∈ Icc 0 M)
      (E : Set Ω) (GoodHigh GoodLow : (Fin n → ℝ) → Ω → Prop) (C : ℝ),
      0 ≤ C →
      (∀ b, (∀ i,b i ∈ Icc 0 M) → (∑ i,(b i-v i)^2) ≤ 4*ε^2*(n:ℝ) →
        μ.real {ω | ¬GoodHigh b ω} ≤ C*exp (-r*(n:ℝ))) →
      (∀ ω ∈ E,∀ a b, (∀ i,a i ∈ Icc 0 M) → (∀ i,b i ∈ Icc 0 M) →
        (∀ i,|a i-b i| ≤ ζ) → GoodHigh b ω → GoodLow a ω) →
      μ.real {ω | ∃ a, (∀ i,a i ∈ Icc 0 M) ∧ (∑ i,(a i-v i)^2) ≤ ε^2*(n:ℝ) ∧
        ¬GoodLow a ω} ≤ μ.real Eᶜ+C*exp (-(r/2)*(n:ℝ)) := by
  classical
  obtain ⟨grid,hgrid,hcover⟩ := interval_mesh (M := M) hζ
  let κ := {x : ℝ // x ∈ grid}
  obtain ⟨α,hα,hcount⟩ := sparse_option_small_entropy (κ := κ) (half_pos hr)
  let ε₀ := sqrt α*ζ
  have hε₀ : 0 < ε₀ := mul_pos (sqrt_pos.mpr hα) hζ
  have heq₀ : ε₀^2=α*ζ^2 := by dsimp [ε₀]; rw [mul_pow,sq_sqrt hα.le]
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hεle
  have heq : ε^2 ≤ α*ζ^2 := by rw [← heq₀]; exact pow_le_pow_left₀ hε.le hεle 2
  intro Ω _ μ _ n v hv E GoodHigh GoodLow C hC hfixed hnear
  let val : κ → ℝ := Subtype.val
  let s : Finset (Fin n → Option κ) := Finset.univ.filter (fun f =>
    ((optionSupport f).card:ℝ) ≤ α*(n:ℝ) ∧
      (∑ i,(optionCube v val f i-v i)^2) ≤ 4*ε^2*(n:ℝ))
  have hsize : (s.card:ℝ) ≤ exp ((r/2)*(n:ℝ)) := by
    simpa only [Fintype.card_fin] using hcount (Fin n) s (fun f hf => by simpa only [Fintype.card_fin] using (Finset.mem_filter.mp hf).2.1)
  let B : (Fin n → Option κ) → Set Ω := fun f => {ω | ¬GoodHigh (optionCube v val f) ω}
  have hsub : {ω | ∃ a, (∀ i,a i ∈ Icc 0 M) ∧ (∑ i,(a i-v i)^2) ≤ ε^2*(n:ℝ) ∧
        ¬GoodLow a ω} ⊆ Eᶜ ∪ ⋃ f ∈ s,B f := by
    intro ω ⟨a,ha,ha2,hbad⟩
    by_cases hE : ω ∈ E
    · obtain ⟨f,hf,hap,hfp⟩ := sparse_cube_approx hζ v a val ha
        (fun x hx => by obtain ⟨y,hy,hyx⟩ := hcover x hx; exact ⟨⟨y,hy⟩,hyx⟩)
        (by
          simp only [Fintype.card_fin]
          exact ha2.trans (mul_le_mul_of_nonneg_right heq (Nat.cast_nonneg n)))
      have hb : ∀ i,optionCube v val f i ∈ Icc 0 M :=
        optionCube_bounds v val hv (fun k => hgrid k.val k.property) f
      have hd : (∑ i,(optionCube v val f i-v i)^2) ≤ 4*ε^2*(n:ℝ) := by
        calc
          _ ≤ ∑ i,4*(a i-v i)^2 := by
            apply Finset.sum_le_sum; intro i _
            have h := hfp i
            have hh := mul_self_le_mul_self (abs_nonneg (optionCube v val f i-v i)) h
            nlinarith only [hh,sq_abs (optionCube v val f i-v i),sq_abs (a i-v i)]
          _ = 4*(∑ i,(a i-v i)^2) := by rw [Finset.mul_sum]
          _ ≤ _ := by linarith
      have hfs : f ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [Fintype.card_fin] using And.intro hf hd⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨f,hfs,fun hg => hbad (hnear ω hE a _ ha hb hap hg)⟩)
    · exact Or.inl hE
  have hsum : (∑ f ∈ s,μ.real (B f)) ≤ (s.card:ℝ)*(C*exp (-r*(n:ℝ))) := by
    calc
      _ ≤ ∑ _f ∈ s,C*exp (-r*(n:ℝ)) := by
        apply Finset.sum_le_sum
        intro f hf
        exact hfixed _ (optionCube_bounds v val hv (fun k => hgrid k.val k.property) f)
          (Finset.mem_filter.mp hf).2.2
      _ = _ := by simp
  apply (measureReal_mono hsub (measure_ne_top _ _)).trans
  apply (measureReal_union_le _ _).trans
  apply add_le_add le_rfl
  apply (measureReal_biUnion_finset_le s B).trans
  apply hsum.trans
  calc
    _ ≤ exp ((r/2)*(n:ℝ))*(C*exp (-r*(n:ℝ))) := mul_le_mul_of_nonneg_right hsize (by positivity)
    _ = _ := by rw [← mul_assoc,mul_comm (exp _) C,mul_assoc,← exp_add]; congr 2; ring
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator

lemma conditional_mesh_size {A L m : ℝ} (hA : 0 < A) (hL : 0 < L) (hm : 0 < m) :
    ∃ ζ : ℝ, 0 < ζ ∧ 2*sqrt A*L*sqrt ζ ≤ m/2 := by
  let r := m/(4*sqrt A*L)
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r^2,sq_pos_of_pos hr,?_⟩
  rw [sqrt_sq hr.le]
  dsimp [r]
  have hd : sqrt A ≠ 0 := (sqrt_pos.mpr hA).ne'
  field_simp
  ring_nf
  rfl

theorem conditional_sparse_uniform {j A L m c : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hL : 0 < L) (hm : 0 < m) (hc : 0 < c) :
    ∃ ε0 : ℝ,0 < ε0 ∧ ∀ ε : ℝ,0 < ε → ε ≤ ε0 →
    ∀ (n : ℕ) [NeZero n] (v : Fin n → ℝ), (∀ i,v i ∈ Icc 0 A) →
    ∀ K : (MatrixCoordinates (Fin n) → ℝ) → Matrix (Fin n) (Fin n) ℝ,
    (∀ g,(K g).IsHermitian) →
    (∀ g,opNorm (goeMatrix (j/(n:ℝ)) g) ≤ 2*sqrt j+1 → opNorm (K g) ≤ L) →
    (∀ b, (∀ i,b i ∈ Icc 0 A) → (∑ i,(b i-v i)^2) ≤ 4*ε^2*(n:ℝ) →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
        {g | ¬(diagonalHessian b (K g)-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef} ≤
        101*exp (-c*(n:ℝ))) →
    (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)).real
      {g | ∃ a, (∀ i,a i ∈ Icc 0 A) ∧ (∑ i,(a i-v i)^2) ≤ ε^2*(n:ℝ) ∧
        ¬(diagonalHessian a (K g)-(m/2) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef} ≤
      103*exp (-(min (1/(π^2*j)) (c/2))*(n:ℝ)) := by
  obtain ⟨ζ,hζ,hζm⟩ := conditional_mesh_size hA hL hm
  obtain ⟨ε0,hε0,hsmall⟩ := sparse_uniform_exponential_shrink (M := A) hζ hc
  refine ⟨ε0,hε0,?_⟩
  intro ε hε hεle n _ v hv K hK hKn hfixed
  let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1)
  let E : Set (MatrixCoordinates (Fin n) → ℝ) := {g | opNorm (goeMatrix (j/(n:ℝ)) g) ≤ 2*sqrt j+1}
  have hevent : μ.real Eᶜ ≤ 2*exp (-(n:ℝ)/(π^2*j)) := by
    change (gaussianCoordinates (MatrixCoordinates (Fin n))).real
      {g | ¬‖matrixOperator (goeMatrix (j/(n:ℝ)) g)‖ ≤ 2*sqrt j+1} ≤ _
    simp only [not_le]
    simpa only [one_pow,_root_.neg_one_mul,Fintype.card_fin] using
      (goe_norm_tail (ι := Fin n) hj (by norm_num : (0:ℝ) ≤ 1))
  have hsparse := hsmall ε hε hεle (MatrixCoordinates (Fin n) → ℝ) μ n v hv E
    (fun b g=>(diagonalHessian b (K g)-m • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef)
    (fun a g=>(diagonalHessian a (K g)-(m/2) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    101 (by norm_num) hfixed (by
      intro g hg a b ha hb hab hh
      have hnorm : ‖K g‖ ≤ L := hKn g hg
      have hd := diagonalHessian_half_holder hA.le hζ.le hL.le ha hb hab (K g) hnorm
      have htrans := hermitian_margin_transfer (diagonalHessian_hermitian a (hK g))
        (diagonalHessian_hermitian b (hK g)) (hd.trans hζm) hh.posSemidef
      have hhalf : m-m/2=m/2 := by ring
      simpa only [hhalf] using htrans)
  apply hsparse.trans
  have h1 : -(n:ℝ)/(π^2*j) ≤ -(min (1/(π^2*j)) (c/2))*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (min_le_left (1/(π^2*j)) (c/2)) (Nat.cast_nonneg n)
    calc
      _ = -((1/(π^2*j))*(n:ℝ)) := by ring
      _ ≤ _ := by linarith only [h]
  have h2 : -(c/2)*(n:ℝ) ≤ -(min (1/(π^2*j)) (c/2))*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1/(π^2*j)) (c/2)) (Nat.cast_nonneg n)
    linarith only [h]
  have h1' := exp_le_exp.mpr h1
  have h2' := exp_le_exp.mpr h2
  nlinarith only [hevent,h1',h2']
end SKGap
end
end

end OAI
