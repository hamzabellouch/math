import OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource
import OAI.NumberTheory.DirichletL.CubicSieve.QuantitativePassage

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

private theorem finite_bounded_rows_smoothed_expand {β : Type*}
    (C : Finset β) (a : β→ℂ) (r : β→O→ℂ) (hr : ∀b∈C,∀z,‖r b z‖≤1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖eisEmbedding z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ))=
      ∑b∈C,∑c∈C,(star (a b)*a c)*∑'z:O,(star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K) := by
  have hs (b c : β) (hb:b∈C) (hc:c∈C) : Summable (fun z:O =>
      (star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K)) := by
    have hW : Summable (fun z:O=>‖W (‖eisEmbedding z‖^2/K)‖) := by
      simpa only [EisensteinSchwartzPoisson.scaledRadialTest_apply] using
        EisensteinSchwartzPoisson.actual_eisenstein_summable_norm
          (EisensteinSchwartzPoisson.scaledRadialTest W K hK)
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z=>norm_nonneg _) _ hW
    intro z
    simp only [norm_mul,norm_star]
    calc
      _ ≤ 1*1*‖W (‖eisEmbedding z‖^2/K)‖ := by
        gcongr
        · exact hr b hb z
        · exact hr c hc z
      _ = _ := by ring
  have he (z:O) : W (‖eisEmbedding z‖^2/K)*(‖∑b∈C,a b*r b z‖^2:ℝ)=
      ∑b∈C,∑c∈C,(star (a b)*a c)*((star (r b z)*r c z)*W (‖eisEmbedding z‖^2/K)) := by
    rw [Complex.sq_norm (∑b∈C,a b*r b z),Complex.normSq_eq_conj_mul_self]
    simp only [map_sum,map_mul,starRingEnd_apply]
    rw [Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun b hb=>summable_sum (fun c hc=>(hs b c hb hc).mul_left _))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Summable.tsum_finsetSum (fun c hc=>(hs b c hb hc).mul_left _)]
  apply Finset.sum_congr rfl
  intro c hc
  exact tsum_mul_left

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma multiplicityRow_norm_le_one (B : Finset ι) (v : ι→ℕ) (z:O) :
    ‖multiplicityRow (fun i=>Ideal.span {p i}) hg B v z‖≤1 := by
  simp only [multiplicityRow,norm_prod,norm_pow]
  calc
    _ ≤ ∏i∈B,(1:ℝ) := by
      apply Finset.prod_le_prod₀ (fun i hi=>by positivity)
      intro i hi
      apply pow_le_one₀ (norm_nonneg _)
      let : Fintype (O⧸Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by simp

omit [DecidableEq ι] in
lemma multiplicityRow_support (B : Finset ι) (v : ι→₀ℕ) (hv : v.support⊆B) (z:O) :
    multiplicityRow (fun i=>Ideal.span {p i}) hg B v z =
      multiplicityRow (fun i=>Ideal.span {p i}) hg v.support v z := by
  unfold multiplicityRow
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

def reopenedCanonicalRow (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (z:O) : ℂ :=
  ∑v∈Q,∑S∈pool.powerset,
    (β v*canonicalSourceCoefficient p hp hcop hg Ψ m f H S)*
    (multiplicityRow (fun i=>Ideal.span {p i}) hg pool v z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)

theorem reopenedCanonicalRow_smoothed_expand
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (β : (ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑'z:O,W (‖eisEmbedding z‖^2/K)*(‖reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z‖^2:ℝ))=
      ∑v₂∈Q,∑v₁∈Q,(star (β v₂)*β v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ Ψ m m f H H W K := by
  let a : (ι→₀ℕ)×Finset ι→ℂ := fun b=>β b.1*canonicalSourceCoefficient p hp hcop hg Ψ m f H b.2
  let r : (ι→₀ℕ)×Finset ι→O→ℂ := fun b z=>
    multiplicityRow (fun i=>Ideal.span {p i}) hg pool b.1 z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg b.2 z
  have hr (b : (ι→₀ℕ)×Finset ι) (hb:b∈Q×ˢpool.powerset) (z:O) : ‖r b z‖≤1 := by
    dsimp [r]
    rw [norm_mul,norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (multiplicityRow_norm_le_one p hg pool b.1 z))).trans
      (finiteSquarefreeRow_norm_le_one _ hg _ _)
  have he:=finite_bounded_rows_smoothed_expand (Q×ˢpool.powerset) a r hr W K hK
  simp only [Finset.sum_product] at he
  change (∑'z:O,W (‖eisEmbedding z‖^2/K)*
    (‖reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f H z‖^2:ℝ))=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro v₂ hv₂
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v₁ hv₁
  simp only [canonicalCubeCorrelation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  have hB₁ : v₁.support⊆v₁.support∪v₂.support:=Finset.subset_union_left
  have hB₂ : v₂.support⊆v₁.support∪v₂.support:=Finset.subset_union_right
  have hr₁ (z:O) : multiplicityRow (fun i=>Ideal.span {p i}) hg pool v₁ z=
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z := by
    rw [multiplicityRow_support p hg pool v₁ (hQ v₁ hv₁),multiplicityRow_support p hg _ v₁ hB₁]
  have hr₂ (z:O) : multiplicityRow (fun i=>Ideal.span {p i}) hg pool v₂ z=
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z := by
    rw [multiplicityRow_support p hg pool v₂ (hQ v₂ hv₂),multiplicityRow_support p hg _ v₂ hB₂]
  simp only [a,r,canonicalCubeSourcePair,star_mul,hr₁,hr₂]
  have ht : (∑'z:O,(star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)*
      star (multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z^3)*
      (multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z^3*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg T z))*W (‖eisEmbedding z‖^2/K))=
      ∑'z:O,(star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z)*
      finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg T z*
      star (multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₂ z^3)*
      multiplicityRow (fun i=>Ideal.span {p i}) hg (v₁.support∪v₂.support) v₁ z^3)*W (‖eisEmbedding z‖^2/K) := by
    apply tsum_congr
    intro z
    ring
  rw [ht]
  ring

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic

def completedDualScale (X r C K U B : ℝ) (D E : Ideal O) : ℝ :=
  r^3*(Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)^3*U*B^3*X/(K^2*C^2)

theorem positive_log_scale_identity (k n b K U B R : ℝ)
    (hk : 0<k) (hn : 0<n) (hb : 0<b) (hK : 0<K) (hU : 0<U) (hB : 0<B) :
    R*Real.exp (-2*Real.log (k/K)+Real.log (n/U)+3*Real.log (b/B))=
      R*(K/k)^2*(n/U)*(b/B)^3 := by
  have h2 : Real.exp ((2:ℝ)*Real.log (k/K))=(k/K)^2 := by
    rw [show (2:ℝ)=(2:ℕ) by rfl,Real.exp_nat_mul,Real.exp_log (div_pos hk hK)]
  have h3 : Real.exp ((3:ℝ)*Real.log (b/B))=(b/B)^3 := by
    rw [show (3:ℝ)=(3:ℕ) by rfl,Real.exp_nat_mul,Real.exp_log (div_pos hb hB)]
  rw [show -2*Real.log (k/K)+Real.log (n/U)+3*Real.log (b/B)=
      -(2*Real.log (k/K))+Real.log (n/U)+3*Real.log (b/B) by ring,
    Real.exp_add,Real.exp_add,Real.exp_neg,h2,h3,Real.exp_log (div_pos hn hU)]
  field_simp

theorem completed_ideal_kernel_scale (X r C K U B : ℝ)
    (D E I J H : Ideal O) (hI : I≠0) (hJ : J≠0) (hH : H≠0)
    (hK : 0<K) (hU : 0<U) (hB : 0<B) :
    completedDualScale X r C K U B D E *
      Real.exp (-2*Real.log ((Ideal.absNorm H:ℝ)/K)+
        Real.log ((Ideal.absNorm I:ℝ)/U)+3*Real.log ((Ideal.absNorm J:ℝ)/B)) =
      r^3*(Ideal.absNorm (D*I):ℝ)*(Ideal.absNorm (E*J):ℝ)^3*X/
        ((Ideal.absNorm H:ℝ)^2*C^2) := by
  have hpos (lengthScale : Ideal O) (hL : lengthScale≠0) : 0<(Ideal.absNorm lengthScale:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hL (Ideal.absNorm_eq_zero_iff.mp hz))
  rw [positive_log_scale_identity _ _ _ _ _ _ _ (hpos H hH) (hpos I hI) (hpos J hJ) hK hU hB]
  simp only [completedDualScale,map_mul,Nat.cast_mul]
  field_simp

end CompletedGauss

open scoped BigOperators
namespace CompletedDyadic

theorem weighted_scale_identity (x t a s : ℝ) (hx : 0<x) (ht : 0<t) :
    x^a*(t*x^3)^(-s)=t^(-s)*x^(a-3*s) := by
  rw [Real.mul_rpow ht.le (pow_nonneg hx.le _),←Real.rpow_natCast_mul hx.le]
  calc
    _ = t^(-s)*(x^a*x^((3:ℝ)*(-s))) := by ring_nf
    _ = _ := by rw [←Real.rpow_add hx]; congr 2; ring

theorem double_kernel_sum_bound (s A β : ℝ) (hs : 0<s) (hsA : s<A) (hβ : β<3*s) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      (∀b : ℕ,Summable (kernelTerm (t*((2:ℝ)^b)^3) s A)) ∧
      Summable (fun b : ℕ => ((2:ℝ)^b)^β*∑'u : ℕ,kernelTerm (t*((2:ℝ)^b)^3) s A u) ∧
      (∑'b : ℕ,((2:ℝ)^b)^β*∑'u : ℕ,kernelTerm (t*((2:ℝ)^b)^3) s A u)≤C*t^(-s) := by
  obtain ⟨Cu,hCu,hu⟩ := kernel_sum_bound s A hs hsA
  let q : ℝ := (2:ℝ)^(β-3*s)
  have hq : q<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0≤q := by dsimp [q]; positivity
  refine ⟨Cu/(1-q),by positivity,?_⟩
  intro t ht
  have hinner (b : ℕ) := hu (t*((2:ℝ)^b)^3) (by positivity)
  have hf0 (b : ℕ) : 0≤((2:ℝ)^b)^β*∑'u : ℕ,kernelTerm (t*((2:ℝ)^b)^3) s A u := by
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (kernelTerm_nonneg _ s A (by positivity))
  have hle (b : ℕ) : ((2:ℝ)^b)^β*∑'u : ℕ,kernelTerm (t*((2:ℝ)^b)^3) s A u≤
      (Cu*t^(-s))*q^b := by
    calc
      _ ≤ ((2:ℝ)^b)^β*(Cu*(t*((2:ℝ)^b)^3)^(-s)) :=
        mul_le_mul_of_nonneg_left (hinner b).2 (by positivity)
      _ = Cu*(((2:ℝ)^b)^β*(t*((2:ℝ)^b)^3)^(-s)) := by ring
      _ = _ := by rw [weighted_scale_identity _ t β s (by positivity) ht,pow_rpow_comm]; dsimp [q]; ring
  have hgeo := (summable_geometric_of_lt_one hq0 hq).mul_left (Cu*t^(-s))
  have hf := hgeo.of_nonneg_of_le hf0 hle
  refine ⟨fun b => (hinner b).1,hf,?_⟩
  have hb := hf.tsum_le_tsum hle hgeo
  rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq] at hb
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hb

def ramifiedScale (ρ q : ℝ) (m : ℕ) : ℝ := ρ*q^m

theorem ramifiedScale_pos (ρ q : ℝ) (hρ : 0<ρ) (hq : 0<q) (m : ℕ) :
    0<ramifiedScale ρ q m := by unfold ramifiedScale; positivity

theorem triple_kernel_sum_bound (s A β ρ q : ℝ)
    (hs : 0<s) (hsA : s<A) (hβ : β<3*s) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t →
      (∀m b : ℕ,Summable (kernelTerm
        (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A)) ∧
      (∀m : ℕ,Summable (fun b : ℕ => ((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u)) ∧
      Summable (fun m : ℕ => (ramifiedScale ρ q m)⁻¹*
        ∑'b : ℕ,((2:ℝ)^b)^β*
          ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u) ∧
      (∑'m : ℕ,(ramifiedScale ρ q m)⁻¹*
        ∑'b : ℕ,((2:ℝ)^b)^β*
          ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u)
        ≤C*t^(-s) := by
  obtain ⟨Cb,hCb,hb⟩ := double_kernel_sum_bound s A β hs hsA hβ
  let v : ℝ := q^(-1-3*s)
  have hv : v<1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hq0 : 0<q := by linarith
  have hv0 : 0≤v := by dsimp [v]; positivity
  let B : ℝ := Cb*ρ^(-1-3*s)
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B/(1-v),by positivity,?_⟩
  intro t ht
  have hm (m : ℕ) := hb (t*(ramifiedScale ρ q m)^3) (by
    have := ramifiedScale_pos ρ q hρ hq0 m
    positivity)
  have hn (m : ℕ) : 0≤(ramifiedScale ρ q m)⁻¹*
      ∑'b : ℕ,((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u := by
    apply mul_nonneg (le_of_lt (inv_pos.mpr (ramifiedScale_pos ρ q hρ hq0 m)))
    apply tsum_nonneg
    intro b
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (kernelTerm_nonneg _ s A (by
      have := ramifiedScale_pos ρ q hρ hq0 m
      positivity))
  have hbound (m : ℕ) : (ramifiedScale ρ q m)⁻¹*
      ∑'b : ℕ,((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u
      ≤(B*t^(-s))*v^m := by
    have hr := ramifiedScale_pos ρ q hρ hq0 m
    calc
      _ ≤ (ramifiedScale ρ q m)⁻¹*(Cb*(t*(ramifiedScale ρ q m)^3)^(-s)) :=
        mul_le_mul_of_nonneg_left (hm m).2.2 (by positivity)
      _ = Cb*((ramifiedScale ρ q m)^(-1:ℝ)*(t*(ramifiedScale ρ q m)^3)^(-s)) := by
        rw [Real.rpow_neg_one]; ring
      _ = Cb*(t^(-s)*(ramifiedScale ρ q m)^(-1-3*s)) := by
        rw [weighted_scale_identity _ t (-1) s hr ht]
      _ = _ := by
        rw [ramifiedScale,Real.mul_rpow hρ.le (pow_nonneg hq0.le _),
          ←Real.rpow_natCast_mul hq0.le,
          mul_comm (m:ℝ) (-1-3*s),Real.rpow_mul_natCast hq0.le]
        dsimp [B,v]
        ring
  have hg := (summable_geometric_of_lt_one hv0 hv).mul_left (B*t^(-s))
  have hf := hg.of_nonneg_of_le hn hbound
  refine ⟨fun m b => (hm m).1 b,fun m => (hm m).2.1,hf,?_⟩
  have hfinal := hf.tsum_le_tsum hbound hg
  rw [tsum_mul_left,tsum_geometric_of_lt_one hv0 hv] at hfinal
  simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hfinal

def normMajorant (deltaLoss A K t r H U B : ℝ) : ℝ :=
  K^deltaLoss/(r*Real.sqrt H)*
    (Real.sqrt K*B^(deltaLoss-1/2)*U^deltaLoss+B^deltaLoss*U^(deltaLoss+1/2))/(1+t*r^3*B^3*U)^A

theorem normMajorant_nonneg (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    0≤normMajorant deltaLoss A K t r H U B := by unfold normMajorant; positivity

theorem normMajorant_eq (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    normMajorant deltaLoss A K t r H U B =
      (K*(U*B))^deltaLoss*(Real.sqrt K+Real.sqrt U*Real.sqrt B)/
        (Real.sqrt B*r*Real.sqrt H*(1+t*r^3*B^3*U)^A) := by
  unfold normMajorant
  rw [Real.mul_rpow hK.le (mul_pos hU hB).le,Real.mul_rpow hU.le hB.le,
    Real.rpow_sub hB,Real.rpow_add hU,←Real.sqrt_eq_rpow B,←Real.sqrt_eq_rpow U]
  have hsB : Real.sqrt B≠0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  field_simp

theorem smooth_energy_le_normMajorant_sq (deltaLoss A K t r H U B : ℝ)
    (hK : 0<K) (ht : 0<t) (hr : 0<r) (hH : 0<H) (hU : 0<U) (hB : 0<B) :
    (K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+t*r^3*B^3*U)^(2*A)
      ≤(normMajorant deltaLoss A K t r H U B)^2 := by
  rw [normMajorant_eq deltaLoss A K t r H U B hK ht hr hH hU hB,div_pow,mul_pow,
    mul_pow,mul_pow,mul_pow,Real.sq_sqrt hB.le,Real.sq_sqrt hH.le]
  have hc : 0≤(K*(U*B))^deltaLoss := by positivity
  have hden : 0<(B*r^2*H)*(1+t*r^3*B^3*U)^(2*A) := by positivity
  have hp (x : ℝ) (hx : 0≤x) (s : ℝ) : (x^s)^2=x^(2*s) := by
    rw [←Real.rpow_mul_natCast hx]
    congr 1
    ring
  rw [hp _ (mul_pos hK (mul_pos hU hB)).le,hp _ (by positivity)]
  rw [div_div]
  apply div_le_div_of_nonneg_right _ hden.le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hcross : 0≤2*Real.sqrt K*(Real.sqrt U*Real.sqrt B) := by positivity
  nlinarith [Real.sq_sqrt hK.le,Real.sq_sqrt hU.le,Real.sq_sqrt hB.le,
    sq_nonneg (Real.sqrt K+Real.sqrt U*Real.sqrt B)]

def tripleTerm (t s A β ρ q : ℝ) (i : ℕ×ℕ×ℕ) : ℝ :=
  (ramifiedScale ρ q i.1)⁻¹*((2:ℝ)^i.2.1)^β*
    kernelTerm (t*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3) s A i.2.2

theorem tripleTerm_nonneg (t s A β ρ q : ℝ) (ht : 0<t) (hρ : 0<ρ) (hq : 0<q)
    (i : ℕ×ℕ×ℕ) : 0≤tripleTerm t s A β ρ q i := by
  unfold tripleTerm
  have hr := ramifiedScale_pos ρ q hρ hq i.1
  exact mul_nonneg (by positivity) (kernelTerm_nonneg _ s A (by positivity) _)

theorem triple_product_kernel_sum_bound (s A β ρ q : ℝ)
    (hs : 0<s) (hsA : s<A) (hβ : β<3*s) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀t : ℝ,0<t → Summable (tripleTerm t s A β ρ q) ∧
      (∑'i : ℕ×ℕ×ℕ,tripleTerm t s A β ρ q i)≤C*t^(-s) := by
  obtain ⟨C,hC,hbound⟩ := triple_kernel_sum_bound s A β ρ q hs hsA hβ hρ hq
  refine ⟨C,hC,?_⟩
  intro t ht
  obtain ⟨hu,hb,hm,hbnd⟩ := hbound t ht
  have hq0 : 0<q := by linarith
  have hpos := tripleTerm_nonneg t s A β ρ q ht hρ hq0
  have hinner (m : ℕ) : Summable (fun j : ℕ×ℕ => tripleTerm t s A β ρ q (m,j)) := by
    apply (summable_prod_of_nonneg (fun j => hpos (m,j))).mpr
    constructor
    · intro b
      simpa only [tripleTerm] using (hu m b).mul_left ((ramifiedScale ρ q m)⁻¹*((2:ℝ)^b)^β)
    · simpa only [tripleTerm,tsum_mul_left,mul_assoc] using
        (hb m).mul_left (ramifiedScale ρ q m)⁻¹
  have hrow (m : ℕ) : (∑'j : ℕ×ℕ,tripleTerm t s A β ρ q (m,j))=
      (ramifiedScale ρ q m)⁻¹*∑'b : ℕ,((2:ℝ)^b)^β*
        ∑'u : ℕ,kernelTerm (t*(ramifiedScale ρ q m)^3*((2:ℝ)^b)^3) s A u := by
    rw [(hinner m).tsum_prod]
    simp only [tripleTerm,tsum_mul_left,mul_assoc]
  have hall : Summable (tripleTerm t s A β ρ q) := by
    apply (summable_prod_of_nonneg hpos).mpr
    exact ⟨hinner,by simpa only [hrow] using hm⟩
  refine ⟨hall,?_⟩
  simpa only [hall.tsum_prod,hrow] using hbnd

theorem normMajorant_eq_triples (deltaLoss A K t H ρ q : ℝ) (i : ℕ×ℕ×ℕ) :
    normMajorant deltaLoss A K t (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)=
      K^deltaLoss/Real.sqrt H*(Real.sqrt K*tripleTerm t deltaLoss A (deltaLoss-1/2) ρ q i+
        tripleTerm t (deltaLoss+1/2) A deltaLoss ρ q i) := by
  simp only [normMajorant,tripleTerm,kernelTerm]
  ring

theorem normMajorant_sum_bound (deltaLoss A ρ q : ℝ)
    (hδ : 0<deltaLoss) (hA : deltaLoss+1/2<A) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y H : ℝ,0<K → 0<Y → 0<H →
      Summable (fun i : ℕ×ℕ×ℕ =>
        normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) ∧
      (∑'i : ℕ×ℕ×ℕ,
        normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1))
        ≤C*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H := by
  obtain ⟨C₁,hC₁,h₁⟩ := triple_product_kernel_sum_bound deltaLoss A (deltaLoss-1/2) ρ q hδ
    (by linarith) (by linarith) hρ hq
  obtain ⟨C₂,hC₂,h₂⟩ := triple_product_kernel_sum_bound (deltaLoss+1/2) A deltaLoss ρ q
    (by linarith) hA (by linarith) hρ hq
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro K Y H hK hY hH
  obtain ⟨hs₁,hb₁⟩ := h₁ Y⁻¹ (by positivity)
  obtain ⟨hs₂,hb₂⟩ := h₂ Y⁻¹ (by positivity)
  simp_rw [normMajorant_eq_triples]
  refine ⟨((hs₁.mul_left (Real.sqrt K)).add hs₂).mul_left (K^deltaLoss/Real.sqrt H),?_⟩
  rw [tsum_mul_left,(hs₁.mul_left (Real.sqrt K)).tsum_add hs₂,tsum_mul_left]
  have hp₁ : (Y⁻¹)^(-deltaLoss)=Y^deltaLoss := by rw [Real.inv_rpow hY.le,Real.rpow_neg hY.le,inv_inv]
  have hp₂ : (Y⁻¹)^(-(deltaLoss+1/2))=Y^deltaLoss*Real.sqrt Y := by
    rw [Real.inv_rpow hY.le,Real.rpow_neg hY.le,inv_inv,Real.rpow_add hY,←Real.sqrt_eq_rpow]
  rw [hp₁] at hb₁
  rw [hp₂] at hb₂
  calc
    _ ≤ K^deltaLoss/Real.sqrt H*(Real.sqrt K*(C₁*Y^deltaLoss)+C₂*(Y^deltaLoss*Real.sqrt Y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hb₁ (Real.sqrt_nonneg _)) hb₂
    _ ≤ K^deltaLoss/Real.sqrt H*((C₁+C₂)*Y^deltaLoss*(Real.sqrt K+Real.sqrt Y)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [mul_nonneg (le_of_lt hC₁) (show 0≤Y^deltaLoss*Real.sqrt Y by positivity),
        mul_nonneg (le_of_lt hC₂) (show 0≤Y^deltaLoss*Real.sqrt K by positivity)]
    _ = _ := by rw [Real.mul_rpow hK.le hY.le]; ring

end CompletedDyadic

namespace CompletedGauss

theorem finite_tsum_energy_bound {κ α : Type*} [Fintype κ]
    (f : α→κ→ℂ) (g : α→ℝ) (hg0 : ∀i,0≤g i) (hg : Summable g)
    (hbound : ∀i,(∑k,‖f i k‖^2)≤(g i)^2) :
    (∀k,Summable (fun i => ‖f i k‖)) ∧
    (∑k,‖∑'i,f i k‖^2)≤(∑'i,g i)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : α→EuclideanSpace ℂ κ := fun i => e.symm (f i)
  have hF (i : α) : ‖F i‖≤g i := by
    apply (sq_le_sq₀ (norm_nonneg _) (hg0 i)).mp
    rw [EuclideanSpace.norm_sq_eq]
    exact hbound i
  have hpoint (k : κ) (i : α) : ‖f i k‖≤g i := by
    apply (sq_le_sq₀ (norm_nonneg _) (hg0 i)).mp
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖f i j‖) (Finset.mem_univ k)).trans
      (hbound i)
  have hsum (k : κ) : Summable (fun i => ‖f i k‖) :=
    hg.of_nonneg_of_le (fun i => norm_nonneg _) (hpoint k)
  have hfp : Summable f := Pi.summable.mpr (fun k => (hsum k).of_norm)
  have he : (∑'i,F i)=e.symm (fun k => ∑'i,f i k) := by
    rw [show (fun i => F i)=(fun i => e.symm (f i)) from rfl,←e.symm.map_tsum]
    congr 1
    funext k
    exact Pi.tsum_apply hfp
  have hn : ‖e.symm (fun k => ∑'i,f i k)‖≤∑'i,g i := by
    rw [←he]
    exact tsum_of_norm_bounded hg.hasSum hF
  refine ⟨hsum,?_⟩
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq] at hs
  exact hs

open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic

def completedSmoothDyadicBlock (V₀ V₁ V₂ W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  ∑n∈S i,∑v∈T i,quadraticRow k.val (primaryGenerator (n*v))*β i n v*
    (V₀ (Real.log ((Ideal.absNorm k.val:ℝ)/K))*
      V₁ (Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2))*
      V₂ (Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))*
      CubicReflectionKernel.paperKernel (Vstar W)
        ((Y⁻¹*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3*(2:ℝ)^i.2.2)*
          Real.exp (-2*Real.log ((Ideal.absNorm k.val:ℝ)/K)+
            Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
              3*Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))))

theorem completed_smooth_series
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y H : ℝ,1≤K → 0<Y → 0<H →
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖β i n v‖≤
        1/(Real.sqrt ((2:ℝ)^i.2.2)*(2:ℝ)^i.2.1*ramifiedScale ρ q i.1*Real.sqrt H)) →
      (∀k,Summable (fun i => ‖completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,
        completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)
        ≤C*(K*Y)^(2*deltaLoss)*(K+Y)/H := by
  obtain ⟨A,hA⟩ := exists_nat_gt (deltaLoss+1/2)
  obtain ⟨Cq,hCq,hquad⟩ := completed_smooth_quadratic V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ hV₀n hV₁n hV₂n W a b ha hsupp hW A (2*deltaLoss) (by positivity)
  obtain ⟨Cs,hCs,hsum⟩ := normMajorant_sum_bound deltaLoss A ρ q hδ hA hρ hq
  refine ⟨2*Cq*Cs^2,by positivity,?_⟩
  intro K Y H hK hY hH S T hS hT β hβ
  have hKp : 0<K := by linarith
  have hqp : 0<q := by linarith
  let g : (ℕ×ℕ×ℕ)→ℝ := fun i => Real.sqrt Cq *
    normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
  have hg0 (i : ℕ×ℕ×ℕ) : 0≤g i := by
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (normMajorant_nonneg _ _ _ _ _ _ _ _
      hKp (by positivity) (ramifiedScale_pos ρ q hρ hqp _) hH (by positivity) (by positivity))
  have henergy (i : ℕ×ℕ×ℕ) :
      (∑k : idealRange K,‖completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)
        ≤(g i)^2 := by
    let U : ℝ := (2:ℝ)^i.2.2
    let B : ℝ := (2:ℝ)^i.2.1
    let r : ℝ := ramifiedScale ρ q i.1
    let R : ℝ := Y⁻¹*r^3*B^3*U
    have hU : 1≤U := one_le_pow₀ (by norm_num)
    have hB : 1≤B := one_le_pow₀ (by norm_num)
    have hUp : 0<U := by positivity
    have hBp : 0<B := by positivity
    have hr : 0<r := ramifiedScale_pos ρ q hρ hqp _
    have hR : 0<R := by dsimp [R]; positivity
    have h := hquad K U B (1/(Real.sqrt U*B*r*Real.sqrt H)) R
      hK hU hB (by positivity) hR (S i) (T i) (hS i) (hT i) (β i) (hβ i)
      (fun k => Real.log ((Ideal.absNorm k.val:ℝ)/K))
      (fun n => Real.log ((Ideal.absNorm n:ℝ)/U))
      (fun v => Real.log ((Ideal.absNorm v:ℝ)/B))
    change (∑k,‖completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)≤_ at h
    apply h.trans
    have he : Cq*(K*(U*B))^(2*deltaLoss)*(K+U*B)*(U*B)*
        (1/(Real.sqrt U*B*r*Real.sqrt H))^2/(1+R)^(2*A)=
        Cq*((K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+R)^(2*(A:ℝ))) := by
      rw [show 2*(A:ℝ)=((2*A:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt hUp.le,Real.sq_sqrt hH.le]
      field_simp

    rw [he]
    have hm := smooth_energy_le_normMajorant_sq deltaLoss A K Y⁻¹ r H U B
      hKp (by positivity) hr hH hUp hBp
    calc
      _ ≤ Cq*(normMajorant deltaLoss A K Y⁻¹ r H U B)^2 := mul_le_mul_of_nonneg_left hm hCq.le
      _ = (g i)^2 := by dsimp [g,U,B,r]; rw [mul_pow,Real.sq_sqrt hCq.le]
  obtain ⟨hs,hb⟩ := hsum K Y H hKp hY hH
  have hm := finite_tsum_energy_bound
    (completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β) g hg0
    (hs.mul_left (Real.sqrt Cq)) henergy
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hb' : (∑'i,g i)≤Real.sqrt Cq*(Cs*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H) := by
    rw [show g=(fun i => Real.sqrt Cq*normMajorant deltaLoss A K Y⁻¹
      (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) from rfl,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (tsum_nonneg hg0) hb' 2
  apply hsq.trans
  have hroot : (Real.sqrt K+Real.sqrt Y)^2≤2*(K+Y) := by
    nlinarith [Real.sq_sqrt hKp.le,Real.sq_sqrt hY.le,
      sq_nonneg (Real.sqrt K-Real.sqrt Y)]
  simp only [mul_pow,div_pow,Real.sq_sqrt hCq.le,Real.sq_sqrt hH.le]
  have hp : ((K*Y)^deltaLoss)^2=(K*Y)^(2*deltaLoss) := by
    rw [←Real.rpow_mul_natCast (mul_pos hKp hY).le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ Cq*(Cs^2*(K*Y)^(2*deltaLoss)*(2*(K+Y))/H) := by
      apply mul_le_mul_of_nonneg_left _ hCq.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) hH.le
    _ = _ := by ring

end CompletedGauss

end

end OAI
