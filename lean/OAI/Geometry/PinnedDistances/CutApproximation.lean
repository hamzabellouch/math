import OAI.Geometry.PinnedDistances.GlobalPotentials

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section

namespace WeakPinned.Cuts
open scoped BigOperators

def tent (δ u : ℝ) : ℝ := max 0 (min (u-δ) (1-δ-u))
lemma tent_nonneg (δ u : ℝ) : 0≤tent δ u := le_max_left _ _
lemma tent_symm (δ u : ℝ) : tent δ (1-u)=tent δ u := by
  unfold tent
  rw [show 1-u-δ=1-δ-u by ring,show 1-δ-(1-u)=u-δ by ring,min_comm]
lemma tent_zero_left {δ u : ℝ} (hu : u≤δ) : tent δ u=0 := by
  unfold tent
  exact max_eq_left ((min_le_left _ _).trans (sub_nonpos.mpr hu))
lemma tent_zero_right {δ u : ℝ} (hu : 1-δ≤u) : tent δ u=0 := by
  rw [← tent_symm]
  exact tent_zero_left (by linarith)
lemma tent_le_one {δ u : ℝ} (hδ : 0≤δ) (hu : u≤1) : tent δ u≤1 := by
  exact max_le (by norm_num) ((min_le_left _ _).trans (by linarith))
lemma tent_lipschitz (δ u v : ℝ) : |tent δ u-tent δ v|≤|u-v| := by
  have hm := abs_max_sub_max_le_max (0:ℝ) (min (u-δ) (1-δ-u)) 0 (min (v-δ) (1-δ-v))
  have hn := abs_min_sub_min_le_max (u-δ) (1-δ-u) (v-δ) (1-δ-v)
  have he : 1-δ-u-(1-δ-v)=-(u-v) := by ring
  have hf : u-δ-(v-δ)=u-v := by ring
  simp only [he,hf,abs_neg,max_self] at hn
  exact hm.trans (max_le (by simp [abs_nonneg]) hn)
lemma tent_positive {δ u : ℝ} (hu : 0<tent δ u) : δ<u ∧ u<1-δ := by
  have h : 0 < min (u-δ) (1-δ-u) := (lt_max_iff.mp hu).resolve_left (lt_irrefl _)
  have := lt_min_iff.mp h
  constructor <;> linarith
lemma tent_lower {δ u : ℝ} (hu : 2*δ≤u) (hu' : u≤1-2*δ) : δ≤tent δ u := by
  exact le_max_iff.mpr (Or.inr (le_min (by linarith) (by linarith)))

def cutError (δ p a : ℝ) : ℝ := |tent δ p-tent δ a|+tent δ a*|p-a|
lemma cutError_nonneg (δ p a : ℝ) : 0≤cutError δ p a :=
  add_nonneg (abs_nonneg _) (mul_nonneg (tent_nonneg _ _) (abs_nonneg _))
lemma cutError_symm (δ p a : ℝ) : cutError δ (1-p) (1-a)=cutError δ p a := by
  simp only [cutError,tent_symm,show 1-p-(1-a)=-(p-a) by ring,abs_neg]
lemma cutError_le {δ p a : ℝ} (hδ : 0≤δ) (ha : a≤1) : cutError δ p a≤2*|p-a| := by
  have := tent_lipschitz δ p a
  have := mul_le_mul_of_nonneg_right (tent_le_one hδ ha) (abs_nonneg (p-a))
  unfold cutError
  linarith
lemma cutError_young {δ p a ε : ℝ} (hδ : 0≤δ) (ha : a≤1) (hε : 0<ε) :
    cutError δ p a≤ε+(p-a)^2/ε := by
  apply (cutError_le hδ ha).trans
  apply (mul_le_mul_iff_left₀ hε).mp
  have he : (ε+(p-a)^2/ε)*ε=ε^2+(p-a)^2 := by field_simp
  rw [he]
  nlinarith [sq_nonneg (|p-a|-ε),sq_abs (p-a)]

/-- Tiny uniform cells have nonzero balanced-cut weight only if their sampled
mass is separated from zero. The variance quadratic then pays the cut error. -/
lemma cutError_tiny {δ p a : ℝ} (hδ : 0<δ) (ha : a<δ/2) (hp : p≤1) :
    cutError δ p a≤(4/δ^2)*(p-a)^2 ∧ cutError δ p a≤(4/δ^2)*(p^2/2) := by
  have hz : tent δ a=0 := tent_zero_left (by linarith)
  rw [cutError,hz,sub_zero,abs_of_nonneg (tent_nonneg _ _),zero_mul,add_zero]
  by_cases hh : tent δ p=0
  · rw [hh]; constructor <;> positivity
  · have ht : 0<tent δ p := lt_of_le_of_ne (tent_nonneg _ _) (Ne.symm hh)
    have hpd := (tent_positive ht).1
    have ht1 := tent_le_one hδ.le hp
    have hd2 : 0<δ^2 := sq_pos_of_pos hδ
    constructor
    · apply ht1.trans
      apply (mul_le_mul_iff_left₀ hd2).mp
      have he : ((4/δ^2)*(p-a)^2)*δ^2=4*(p-a)^2 := by field_simp
      rw [he]
      nlinarith [sq_nonneg (p-a-δ/2),mul_nonneg (by linarith : 0≤p-a-δ/2) hδ.le]
    · apply ht1.trans
      apply (mul_le_mul_iff_left₀ hd2).mp
      have he : ((4/δ^2)*(p^2/2))*δ^2=2*p^2 := by field_simp; ring
      rw [he]
      nlinarith [sq_nonneg (p-δ),mul_nonneg (by linarith : 0≤p-δ) hδ.le]
end WeakPinned.Cuts

namespace WeakPinned.Variance
open scoped BigOperators
open Cuts
variable {P : Type u1} {I : Type u2} [Fintype P] [Fintype I] [DecidableEq P]

noncomputable def familyCutError (w : I → ℝ) (B : I → Finset P) (δ : ℝ) (C : Finset P) : ℝ :=
  ∑ i, w i*cutError δ (cellProb (B i) C) (cellProb Finset.univ C)

lemma familyCutError_bound (w : I → ℝ) (B : I → Finset P) (T δ ε : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hδ : 0<δ) (hε : 0<ε)
    (hk : ∀ i, 2/((B i).card:ℝ)≤δ) (C : Finset P)
    (hlarge : δ/2≤cellProb Finset.univ C → T<C.card)
    (hpair : δ/2≤cellProb Finset.univ C → 1≤(8/δ^2)*pairCell Finset.univ C) :
    familyCutError w B δ C≤(8*ε/δ^2)*pairCell Finset.univ C+
      (1/ε+4/δ^2)*varianceCell w B T C := by
  have hv : 0≤varianceCell w B T C := varianceCell_nonneg w B T hw C
  by_cases ha : δ/2≤cellProb Finset.univ C
  · have he := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (cutError_young (p:=cellProb (B i) C) hδ.le (cellProb_le_one (Finset.univ : Finset P) C) hε) (hw i))
    change familyCutError w B δ C≤_ at he
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,← mul_div_assoc,← Finset.sum_div] at he
    have hvf : varianceCell w B T C=∑ i, w i*(cellProb (B i) C-cellProb Finset.univ C)^2 := by
      simp only [varianceCell,ite_eq_left (hlarge ha)]
    rw [← hvf] at he
    have he2 : (∑ i, w i)*ε≤ε := by nlinarith
    have he3 : ε≤(8*ε/δ^2)*pairCell Finset.univ C := by
      have hh := mul_le_mul_of_nonneg_left (hpair ha) hε.le
      calc
        ε = ε*1 := by ring
        _ ≤ ε*((8/δ^2)*pairCell Finset.univ C) := hh
        _ = _ := by ring
    have hx : 0≤(4/δ^2)*varianceCell w B T C := mul_nonneg (by positivity) hv
    have hh : varianceCell w B T C/ε=(1/ε)*varianceCell w B T C := by ring
    rw [hh] at he
    nlinarith
  · have hat : cellProb Finset.univ C<δ/2 := lt_of_not_ge ha
    have hb : familyCutError w B δ C≤(4/δ^2)*varianceCell w B T C := by
      unfold familyCutError varianceCell
      split_ifs with hl
      · rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hh := (cutError_tiny hδ hat (cellProb_le_one (B i) C)).1
        have hm := mul_le_mul_of_nonneg_left hh (hw i)
        convert hm using 1; ring
      · simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        by_cases hpk : 2/((B i).card:ℝ)≤cellProb (B i) C
        · rw [ite_eq_left hpk]
          have hh := (cutError_tiny hδ hat (cellProb_le_one (B i) C)).2
          have hm := mul_le_mul_of_nonneg_left hh (hw i)
          convert hm using 1; ring
        · rw [ite_eq_right hpk]
          have hp : cellProb (B i) C≤δ := (le_of_lt (lt_of_not_ge hpk)).trans (hk i)
          simp only [cutError,tent_zero_left hp,tent_zero_left (show cellProb Finset.univ C≤δ by linarith),
            sub_self,abs_zero,zero_mul,add_zero,mul_zero]
          norm_num
    have hx : 0≤(8*ε/δ^2)*pairCell Finset.univ C := mul_nonneg (by positivity) (pairCell_nonneg _ _)
    have hy : 0≤(1/ε)*varianceCell w B T C := mul_nonneg (by positivity) hv
    nlinarith
end WeakPinned.Variance

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u3} {I : Type u4} [Fintype P] [Fintype I] [DecidableEq P]

lemma balanced_cell_size (δ : ℝ) (hδ : 0<δ) (hn : 4≤δ*(Fintype.card P:ℝ))
    (C : Finset P) (ha : δ/2≤cellProb Finset.univ C) : 2≤C.card := by
  have hn0 : (0:ℝ)<Fintype.card P := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hδ.le h
    linarith
  simp only [cellProb,Finset.univ_inter,Finset.card_univ] at ha
  have hh := (le_div_iff₀ hn0).mp ha
  exact_mod_cast (show (2:ℝ)≤C.card by nlinarith)

lemma balanced_cell_pair (δ : ℝ) (hδ : 0<δ) (hn : 4≤δ*(Fintype.card P:ℝ))
    (C : Finset P) (ha : δ/2≤cellProb Finset.univ C) :
    1≤(8/δ^2)*pairCell Finset.univ C := by
  have hpair := (uniform_pair_comparison C (balanced_cell_size δ hδ hn C ha)).1
  have han := cellProb_nonneg (Finset.univ : Finset P) C
  have hh : δ^2≤8*pairCell Finset.univ C := by nlinarith
  have he : (8/δ^2)*pairCell Finset.univ C=(8*pairCell Finset.univ C)/δ^2 := by ring
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by simpa using hh)

/-- Integrated approximation to balanced tree cuts, quantitatively, with no
selection of a realizing grid and no hidden count of occurrence multiplicities. -/
lemma weighted_cut_approximation (m : Finset P → ℝ) (hm : ∀ C, 0 ≤ m C)
    (w : I → ℝ) (B : I → Finset P) (T δ ε : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hδ : 0<δ) (hε : 0<ε)
    (hn : 4≤δ*(Fintype.card P:ℝ)) (hT : T<δ*(Fintype.card P:ℝ)/2)
    (hk : ∀ i, 2/((B i).card:ℝ)≤δ) :
    weightedIntegral m (familyCutError w B δ)≤
      (8*ε/δ^2)*weightedIntegral m (pairCell Finset.univ)+
      (1/ε+4/δ^2)*weightedIntegral m (varianceCell w B T) := by
  have hn0 : (0:ℝ)<Fintype.card P := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hδ.le h
    linarith
  have hpoint (C : Finset P) := familyCutError_bound w B T δ ε hw hW hδ hε hk C
    (fun ha => by
      simp only [cellProb,Finset.univ_inter,Finset.card_univ] at ha
      have hh := (le_div_iff₀ hn0).mp ha
      linarith) (balanced_cell_pair δ hδ hn C)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun C _ =>
    mul_le_mul_of_nonneg_left (hpoint C) (hm C))
  change weightedIntegral m (familyCutError w B δ)≤_ at hh
  convert hh using 1
  simp only [weightedIntegral,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> ring

end WeakPinned.Variance

namespace WeakPinned
open Filter
open scoped Topology

/-- A Young estimate for every fixed positive ε implies the required little-o
cut approximation. D is the actual (positive) overlap normalization. -/
lemma cut_approximation_rate (E V W D : ℕ → ℝ) (δ K : ℝ) (hδ : 0<δ) (hK : 0<K)
    (hE : ∀ j, 0≤E j) (hD : ∀ j, 0<D j)
    (hW : ∀ᶠ j in atTop, W j≤K*D j)
    (hV : Tendsto (fun j => V j/D j) atTop (𝓝 0))
    (hb : ∀ ε : ℝ, 0<ε → ∀ᶠ j in atTop,
      E j≤(8*ε/δ^2)*W j+(1/ε+4/δ^2)*V j) :
    Tendsto (fun j => E j/D j) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ζ hζ
  let ε : ℝ := ζ*δ^2/(32*K)
  have hε : 0<ε := by dsimp [ε]; positivity
  have heq : (8*ε/δ^2)*K=ζ/4 := by dsimp [ε]; field_simp; ring
  have hc : 0<1/ε+4/δ^2 := by positivity
  have hh : ∀ᶠ j in atTop, |(1/ε+4/δ^2)*(V j/D j)|<ζ/2 := by
    have hh0 : Tendsto (fun j => (1/ε+4/δ^2)*(V j/D j)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hV.const_mul (1/ε+4/δ^2)
    exact (hh0.eventually (Metric.ball_mem_nhds (0:ℝ) (half_pos hζ))).mono
      (fun j hj => by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hj)
  have hh' : ∀ᶠ j in atTop, |E j/D j-0|<ζ := by
    filter_upwards [hb ε hε,hW,hh] with j hj hjw hjv
    have hn := div_nonneg (hE j) (hD j).le
    rw [sub_zero,abs_of_nonneg hn]
    have hp := mul_le_mul_of_nonneg_left hjw (show 0≤8*ε/δ^2 by positivity)
    have hle : E j/D j≤(8*ε/δ^2)*K+(1/ε+4/δ^2)*(V j/D j) := by
      apply (div_le_iff₀ (hD j)).mpr
      have he : ((8*ε/δ^2)*K+(1/ε+4/δ^2)*(V j/D j))*D j =
        (8*ε/δ^2)*(K*D j)+(1/ε+4/δ^2)*V j := by field_simp [ne_of_gt (hD j)]
      rw [he]
      linarith
    rw [heq] at hle
    have := (le_abs_self _).trans_lt hjv
    linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh'
  exact ⟨N,fun j hj => by simpa only [Real.dist_eq] using hN j hj⟩
end WeakPinned

namespace WeakPinned
open Filter Variance Global
open scoped Topology BigOperators
variable {P : ℕ → Type u5} {I : ℕ → Type u6} [∀ j, Fintype (P j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (P j)]

lemma variance_to_cut_rate (m : ∀ j, Finset (P j) → ℝ) (hm : ∀ j C, 0 ≤ m j C)
    (w : ∀ j, I j → ℝ) (B : ∀ j, I j → Finset (P j)) (D : ℕ → ℝ) (γ c δ : ℝ)
    (hD : ∀ j, 0<D j) (hδ : 0<δ) (hγ : 0<γ) (hc : 0<c)
    (hn : Tendsto (fun j => (Fintype.card (P j):ℝ)) atTop atTop)
    (hw : ∀ j i, 0≤w j i) (hW : ∀ j, (∑ i, w j i)≤1)
    (hsize : ∀ j i, (Fintype.card (P j):ℝ)^γ≤((B j i).card:ℝ))
    (hWD : ∀ j, weightedIntegral (m j) (pairCell Finset.univ)≤D j)
    (hV : Tendsto (fun j => weightedIntegral (m j)
      (varianceCell (w j) (B j) ((Fintype.card (P j):ℝ)^(1-c)))/D j) atTop (𝓝 0)) :
    Tendsto (fun j => weightedIntegral (m j) (familyCutError (w j) (B j) δ)/D j) atTop (𝓝 0) := by
  let n := fun j => (Fintype.card (P j):ℝ)
  have hnγ : Tendsto (fun j => n j^γ) atTop atTop := (tendsto_rpow_atTop hγ).comp hn
  have hnc : Tendsto (fun j => n j^(-c)) atTop (𝓝 0) := (tendsto_rpow_neg_atTop hc).comp hn
  apply cut_approximation_rate _ _ (fun j => weightedIntegral (m j) (pairCell Finset.univ)) D δ 1 hδ (by norm_num)
    (fun j => Finset.sum_nonneg (fun C _ => mul_nonneg (hm j C)
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hw j i) (Cuts.cutError_nonneg _ _ _))))) hD
    (Eventually.of_forall (fun j => by simpa using hWD j)) hV
  intro ε hε
  filter_upwards [hn.eventually (eventually_gt_atTop (4/δ)),
    hnγ.eventually (eventually_ge_atTop (2/δ)), hnc.eventually (gt_mem_nhds (half_pos hδ))] with j hj hjγ hjc
  have hn0 : 0<n j := (by positivity : 0<4/δ).trans hj
  have hnj : 4≤δ*n j := by
    have hh := (div_lt_iff₀ hδ).mp hj
    nlinarith
  have hT : n j^(1-c)<δ*n j/2 := by
    rw [sub_eq_add_neg,Real.rpow_add hn0,Real.rpow_one]
    nlinarith
  have hk (i) : 2/((B j i).card:ℝ)≤δ := by
    have hbs : 0<((B j i).card:ℝ) := (Real.rpow_pos_of_pos hn0 γ).trans_le (hsize j i)
    apply (div_le_iff₀ hbs).mpr
    have hh := (div_le_iff₀ hδ).mp (hjγ.trans (hsize j i))
    nlinarith
  exact weighted_cut_approximation (m j) (hm j) (w j) (B j) (n j^(1-c)) δ ε
    (hw j) (hW j) hδ hε hnj hT hk

end WeakPinned

namespace WeakPinned
open Filter Variance Global
open scoped Topology BigOperators
variable {V : ℕ → Type u7} {I : ℕ → Type u8} {K : ℕ → Type u9} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

/-- Cut approximation for both sampling families, normalized by W₂+A+1
    and hence by W in the unbounded regime. -/
theorem sampling_cut_approximation_rates (δ : ℝ) (hδ : 0<δ) (hθ : 0<θ)
    (hγ : 0<γ) (hγ1 : γ<1) (hc : 0<c) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y ∈ (G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    Tendsto (fun j => weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
        (familyCutError (G j).fiberWeight (G j).targets δ)/
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) ∧
    Tendsto (fun j => weightedIntegral (totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
        (familyCutError ((G j).retainedWeight ((Fintype.card (V j):ℝ)^γ))
          ((G j).retainedSet ((Fintype.card (V j):ℝ)^γ)) δ)/
      (overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1)) atTop (𝓝 0) := by
  have hv := sampling_variance_rates G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  let m := fun j => totalMass (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let D := fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1
  have hD (j) : 0<D j := by dsimp [D]; linarith [overlapScale_nonneg (Z₁ j) (Z₂ j) (h₁ j) (h₂ j),potentialScale_nonneg (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)]
  have hWD (j) : weightedIntegral (m j) (pairCell Finset.univ)≤D j := by
    change overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)≤_
    dsimp [D]
    linarith [potentialScale_nonneg (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)]
  have hpos (j) : 0<(G j).edgeCount := (hG j).edgeCount_pos (by linarith [hηb j])
  constructor
  · exact variance_to_cut_rate m (fun j => totalMass_nonneg _ _ _ _)
      (fun j => (G j).fiberWeight) (fun j => (G j).targets) D γ c δ hD hδ hγ hc hn
      (fun j => (G j).fiberWeight_nonneg) (fun j => ((G j).sum_fiberWeight (hpos j)).le)
      (fun j i => ((hG j).fiber i).le) hWD hv.1
  · apply variance_to_cut_rate m (fun j => totalMass_nonneg _ _ _ _)
      (fun j => (G j).retainedWeight ((Fintype.card (V j):ℝ)^γ))
      (fun j => (G j).retainedSet ((Fintype.card (V j):ℝ)^γ)) D γ c δ hD hδ hγ hc hn
      (fun j => (G j).retainedWeight_nonneg _) (fun j => (G j).sum_retainedWeight _ (hpos j)) _ hWD hv.2
    intro j y
    apply (G j).retainedSet_size
    have hn1 : (1:ℝ)≤Fintype.card (V j) := by exact_mod_cast (by have := (hG j).card_ge; omega : 1≤Fintype.card (V j))
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hγ1.le
end WeakPinned

end
end
end
end
end
end
end
end
end
end
end

end OAI
