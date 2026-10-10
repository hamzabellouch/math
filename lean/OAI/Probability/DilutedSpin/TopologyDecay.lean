import OAI.Probability.DilutedSpin.MeasurableEncoding
import OAI.Probability.DilutedSpin.PatternComparison
import OAI.Probability.DilutedSpin.QSubtreePotential

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
noncomputable local instance finiteMapDecEq (β : Type) : DecidableEq β := Classical.decEq β
namespace FiniteLaw
variable {Ω β : Type} [Fintype Ω] [Fintype β]
noncomputable def map (P : FiniteLaw Ω) (f : Ω → β) : FiniteLaw β where
  weight b := P.expect (fun a => if f a=b then 1 else 0)
  nonneg b := P.expect_nonneg (fun a => by split_ifs <;> norm_num)
  total := by
    classical
    rw [← expect_fintype_sum]
    simp

lemma expect_map (P : FiniteLaw Ω) (f : Ω → β) (g : β → ℝ) :
    (P.map f).expect g=P.expect (fun a => g (f a)) := by
  classical
  change (∑ b, P.expect (fun a => if f a=b then 1 else 0)*g b)=_
  simp_rw [← expect_mul_right]
  rw [← expect_fintype_sum]
  apply expect_congr
  intro a
  simp

lemma expect_pi_map {ι : Type} [Fintype ι] [DecidableEq ι] {α β : ι → Type}
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → β i)
    (g : ((i : ι) → β i) → ℝ) :
    (pi Q).expect (fun a => g (fun i => f i (a i))) =
      (pi (fun i => (Q i).map (f i))).expect g := by
  classical
  have hpoint (a : (i : ι) → α i) :
      g (fun i => f i (a i)) = ∑ b, (∏ i, (if f i (a i)=b i then (1:ℝ) else 0))*g b := by
    have hh (b : (i : ι) → β i) :
        (∏ i, (if f i (a i)=b i then (1:ℝ) else 0)) = if (fun i => f i (a i))=b then 1 else 0 := by
      by_cases h : (fun i => f i (a i))=b
      · subst b; simp
      · rw [ite_eq_right h]
        obtain ⟨i,hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    simp_rw [hh]
    simp
  calc
    _ = (pi Q).expect (fun a => ∑ b, (∏ i, (if f i (a i)=b i then (1:ℝ) else 0))*g b) :=
      (pi Q).expect_congr hpoint
    _ = ∑ b, (∏ i, (Q i).expect (fun a => if f i a=b i then (1:ℝ) else 0))*g b := by
      rw [expect_fintype_sum]
      simp only [expect_mul_right]
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      exact expect_pi_product Q (fun i a => if f i a=b i then 1 else 0)
    _ = _ := rfl

lemma expect_bool (P : FiniteLaw Ω) (v : Ω → Spin) (f : Spin → ℝ) :
    P.expect (fun a => f (v a)) =
      ∑ s : Spin, ((1+spin s * P.expect (fun a => spin (v a)))/2)*f s := by
  have hid (s : Spin) : f s=(f true+f false)/2 + spin s*((f true-f false)/2) := by
    cases s <;> simp [spin] <;> ring
  calc
    _ = P.expect (fun a => (f true+f false)/2 + spin (v a)*((f true-f false)/2)) :=
      P.expect_congr (fun a => hid (v a))
    _ = _ := by simp only [expect_add,expect_const,expect_mul_right,Fintype.sum_bool,spin,
      Bool.false_eq_true,↓reduceIte,neg_one_mul,one_mul]; ring

lemma map_spin_weight (P : FiniteLaw Ω) (v : Ω → Spin)
    (hv : P.expect (fun a => spin (v a)) ∈ Set.Ioo (-1) 1) (s : Spin) :
    (P.map v).weight s=q (Real.artanh (P.expect (fun a => spin (v a)))) s := by
  classical
  dsimp only [map]
  have hc : (fun a : Ω => @ite ℝ (v a=s) (finiteMapDecEq Spin (v a) s) 1 0) =
      (fun a : Ω => if v a=s then (1:ℝ) else 0) := by funext a; split_ifs <;> rfl
  rw [hc]
  rw [expect_bool P v (fun t => if t=s then 1 else 0),q_artanh _ hv]
  simp

noncomputable def spinLog {ι : Type} [Fintype ι] (F : (ι → Spin) → ℝ) (x : ι → ℝ) : ℝ :=
  Real.log (∑ s : ι → Spin, (∏ i, q (x i) (s i))*Real.exp (F s))

lemma logMean_pi_spin {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i, Fintype (α i)] (Q : (i : ι) → FiniteLaw (α i))
    (v : (i : ι) → α i → Spin) (F : (ι → Spin) → ℝ)
    (hv : ∀ i, (Q i).expect (fun a => spin (v i a)) ∈ Set.Ioo (-1) 1) :
    (pi Q).logMean 1 (fun a => F (fun i => v i (a i))) =
      spinLog F (fun i => Real.artanh ((Q i).expect (fun a => spin (v i a)))) := by
  change Real.log ((pi Q).expect (fun a => Real.exp (1*F (fun i => v i (a i)))))/1=_
  simp only [one_mul,div_one]
  rw [expect_pi_map Q v (fun s => Real.exp (F s))]
  simp only [expect,pi,map_spin_weight _ _ (hv _),spinLog]
  congr 1
  congr!

end FiniteLaw
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.PrescribedTree
open ReducedTopology DepthAverage Filter Set
open scoped BigOperators Topology
noncomputable local instance topologyDecayDecidableEq (valueType : Type) :
    DecidableEq valueType := Classical.decEq valueType
noncomputable local instance topologyDecayDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition

lemma ceil_boundary_bound {L : ℕ} (hL : 0<L) {η : ℝ} (hη : 0≤η) :
    (2*(⌈η*(L:ℝ)⌉₊+1:ℕ):ℝ)/(L:ℝ) ≤ 2*η+4/(L:ℝ) := by
  have hh := (Nat.ceil_lt_add_one (mul_nonneg hη (Nat.cast_nonneg L))).le
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  apply (div_le_iff₀ hLr).mpr
  push_cast
  rw [add_mul,div_mul_cancel₀ _ hLr.ne']
  nlinarith

lemma qExpect_subtree_eta_bound {L : ℕ} [NeZero L] (K k : ℕ)
    (F : PrescribedTree L → ℝ) (h0 : ∀ T, 0≤F T) (h1 : ∀ T, F T≤1)
    {η : ℝ} (hη : 0≤η) :
    qExpect (grid L 0 L) (subtreePotential K F) k (single L) ≤
      ∑ S∈boundedTopologies K, shapeCharge k S *
        (average (regularOverlapDomain S L η) (fun q => F (S.realize L 0 (fun v => q v)))+
          shapeBadConstant S*(2*η+4/(L:ℝ))) := by
  apply (qExpect_subtree_regular_bound K k F h0 h1 (Nat.le_ceil (η*(L:ℝ)))).trans
  apply Finset.sum_le_sum
  intro S _
  apply mul_le_mul_of_nonneg_left _ (shapeCharge_nonneg k S)
  apply add_le_add le_rfl
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (ceil_boundary_bound (NeZero.pos L) hη) (shapeBadConstant_nonneg S)

 
theorem qSubtree_limsup_tendsto (K k : ℕ)
    (F : (L : ℕ) → ℕ → PrescribedTree (L+1) → ℝ)
    (h0 : ∀ L n T, 0≤F L n T) (h1 : ∀ L n T, F L n T≤1)
    (hdecay : ∀ S : ReducedTopology, ∀ η : ℝ, 0<η →
      Tendsto (fun L => limsup (fun n => average (regularOverlapDomain S (L+1) η)
        (fun q => F L n (S.realize (L+1) 0 (fun v => q v)))) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (fun n => qExpect (grid (L+1) 0 (L+1))
      (subtreePotential K (F L n)) k (single (L+1))) atTop) atTop (𝓝 0) := by
  let a (L n : ℕ) := qExpect (grid (L+1) 0 (L+1)) (subtreePotential K (F L n)) k (single (L+1))
  have ha (L n : ℕ) : 0≤a L n := qExpect_nonneg _ (grid_strictMono (by omega)).monotone grid_nonneg
    _ (subtreePotential_nonneg _ (h0 L n)) _ _
  have hb (L : ℕ) (η : ℝ) (hη : 0≤η) : limsup (a L) atTop≤
      ∑ S∈boundedTopologies K, shapeCharge k S *
        (limsup (fun n => average (regularOverlapDomain S (L+1) η)
          (fun q => F L n (S.realize (L+1) 0 (fun v => q v)))) atTop +
          shapeBadConstant S*(2*η+4/(L+1:ℕ))) := by
    apply limsup_finite_linear_bound _ _ _ _ _ (fun S _ => shapeCharge_nonneg k S) (ha L)
      (fun S _ n => average_le_const _ _ (by norm_num) (fun q _ => h1 L n _))
    intro n
    exact qExpect_subtree_eta_bound K k (F L n) (h0 L n) (h1 L n) hη
  have hl (L : ℕ) : 0≤limsup (a L) atTop := by
    have hcap (n : ℕ) : a L n≤∑ S∈boundedTopologies K, shapeCharge k S*(1+shapeBadConstant S*(2+4/(L+1:ℕ))) := by
      apply (qExpect_subtree_eta_bound K k (F L n) (h0 L n) (h1 L n) (by norm_num : (0:ℝ)≤1)).trans
      apply Finset.sum_le_sum
      intro S _
      apply mul_le_mul_of_nonneg_left _ (shapeCharge_nonneg k S)
      apply add_le_add
      · exact average_le_const _ _ (by norm_num) (fun q _ => h1 L n _)
      · norm_num
    apply le_limsup_of_le (show IsBoundedUnder (·≤·) atTop (a L) from
      isBoundedUnder_of_eventually_le (Eventually.of_forall hcap))
    intro b hb
    obtain ⟨n,hn⟩ := hb.exists
    exact (ha L n).trans hn
  let C := ∑ S∈boundedTopologies K, shapeCharge k S*shapeBadConstant S*2
  have hC : 0≤C := Finset.sum_nonneg (fun S _ => by
    have := shapeCharge_nonneg k S; have := shapeBadConstant_nonneg S; positivity)
  apply squeeze_triangle_grid_zero _ C hl hC
    (fun η L => ∑ S∈boundedTopologies K, shapeCharge k S *
      (limsup (fun n => average (regularOverlapDomain S (L+1) η)
        (fun q => F L n (S.realize (L+1) 0 (fun v => q v)))) atTop +
        shapeBadConstant S*(2*η+4/(L+1:ℕ)))) _ (fun η hη L => hb L η hη.le)
  intro η hη
  have ht : Tendsto (fun L : ℕ => (4:ℝ)/(L+1:ℕ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hh := tendsto_finsetSum (boundedTopologies K) (fun S _ =>
    ((hdecay S η hη).add (((tendsto_const_nhds (x := 2*η)).add ht).const_mul (shapeBadConstant S))).const_mul (shapeCharge k S))
  convert hh using 1
  simp only [zero_add,add_zero,C,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  ring

end DilutedSpinGlass.PrescribedTree

end

end OAI
