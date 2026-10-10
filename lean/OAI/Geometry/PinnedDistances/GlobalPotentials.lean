import OAI.Geometry.PinnedDistances.MinPotentials

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16

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

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

def placeUnion : Finset (NumberField.FinitePlace K)  := by
  classical
  exact badPlaces Z₁ h₁ ∪ badPlaces Z₂ h₂

def average (f : Depth P → Depth P → ℝ) : ℝ :=
  (∑ v : NumberField.InfinitePlace K, Arithmetic.archWeight v *
    ∫ ω, f (arch Z₁ v ω) (arch Z₂ v ω) ∂Grid.fullLaw) +
  (Module.finrank ℚ K : ℝ)⁻¹ * ∑ v ∈ placeUnion Z₁ Z₂ h₁ h₂,
    f (finite Z₁ h₁ v) (finite Z₂ h₂ v)

def AverageIntegrable (f : Depth P → Depth P → ℝ) : Prop :=
  ∀ v : NumberField.InfinitePlace K,
    Integrable (fun ω => f (arch Z₁ v ω) (arch Z₂ v ω)) Grid.fullLaw

lemma average_mono {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g)
    (hfg : ∀ d d', f d d'≤g d d') :
    average Z₁ Z₂ h₁ h₂ f≤average Z₁ Z₂ h₁ h₂ g  := by
  classical
  apply add_le_add
  · apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (integral_mono (hi v) (hj v) (fun ω => hfg _ _))
      (Arithmetic.archWeight_nonneg v)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun v _ => hfg _ _)

lemma average_add {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => f d d'+g d d')=
      average Z₁ Z₂ h₁ h₂ f+average Z₁ Z₂ h₁ h₂ g  := by
  classical
  unfold average
  simp only [integral_add (hi _) (hj _),mul_add,Finset.sum_add_distrib]
  ring

lemma average_mul (f : Depth P → Depth P → ℝ) (c : ℝ) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => c*f d d')=c*average Z₁ Z₂ h₁ h₂ f  := by
  classical
  unfold average
  simp only [integral_const_mul,Finset.mul_sum,mul_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro v _ <;> ring

lemma average_sum {J : Type u3} [Fintype J] (f : J → Depth P → Depth P → ℝ)
    (hi : ∀ j, AverageIntegrable Z₁ Z₂ (f j)) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => ∑ j, f j d d')=
      ∑ j, average Z₁ Z₂ h₁ h₂ (f j)  := by
  classical
  unfold average
  simp_rw [integral_finsetSum _ (fun j _ => hi j _),Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_comm (s:=placeUnion Z₁ Z₂ h₁ h₂)]
  simp only [Finset.sum_add_distrib]

lemma average_potential_left (hn : 2≤Fintype.card P) (x : P) :
    average Z₁ Z₂ h₁ h₂ (fun d _ => d.potential x)=S Z₁ h₁ x  := by
  classical
  unfold average S
  congr 2
  exact sum_finite_potential h₁ hn _ Finset.subset_union_left x

lemma average_potential_right (hn : 2≤Fintype.card P) (x : P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d' => d'.potential x)=S Z₂ h₂ x  := by
  classical
  unfold average S
  congr 2
  exact sum_finite_potential h₂ hn _ Finset.subset_union_right x

lemma average_mass_left (hn : 2≤Fintype.card P) (C : Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun d _ => d.mass C)=cellMass Z₁ h₁ C  := by
  classical
  unfold average cellMass
  congr 2
  exact sum_finite_mass h₁ hn _ Finset.subset_union_left C

lemma average_mass_right (hn : 2≤Fintype.card P) (C : Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d' => d'.mass C)=cellMass Z₂ h₂ C  := by
  classical
  unfold average cellMass
  congr 2
  exact sum_finite_mass h₂ hn _ Finset.subset_union_right C

omit [NumberField K] in
include h₁ in
lemma integrable_potential_left (hn : 2≤Fintype.card P) (x : P) :
    AverageIntegrable Z₁ Z₂ (fun d _ => d.potential x) :=
  fun v => Depth.integrable_potential_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn x

omit [NumberField K] in
include h₂ in
lemma integrable_potential_right (hn : 2≤Fintype.card P) (x : P) :
    AverageIntegrable Z₁ Z₂ (fun _ d' => d'.potential x) :=
  fun v => Depth.integrable_potential_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn x

omit [NumberField K] in
include h₁ in
lemma integrable_mass_left (hn : 2≤Fintype.card P) (C : Finset P) :
    AverageIntegrable Z₁ Z₂ (fun d _ => d.mass C) :=
  fun v => Depth.integrable_mass_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn C

omit [NumberField K] in
include h₂ in
lemma integrable_mass_right (hn : 2≤Fintype.card P) (C : Finset P) :
    AverageIntegrable Z₁ Z₂ (fun _ d' => d'.mass C) :=
  fun v => Depth.integrable_mass_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn C

end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable {K : Type u5} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
def potentialEval (p : P → ℝ) (d d' : Depth P) : ℝ := ∑ y, p y*(d.potential y+d'.potential y)
omit Z₁ Z₂ h₁ h₂ in
def massEval (q : Finset P → ℝ) (d d' : Depth P) : ℝ :=
  weightedIntegral d.mass q+weightedIntegral d'.mass q

omit [NumberField K] in
include h₁ h₂ in
lemma integrable_potentialEval (hn : 2≤Fintype.card P) (p : P → ℝ) :
    AverageIntegrable Z₁ Z₂ (potentialEval p) := by
  intro v
  exact integrable_finsetSum (s:=Finset.univ) (fun y _ =>
    ((integrable_potential_left Z₁ Z₂ h₁ hn y v).add
      (integrable_potential_right Z₁ Z₂ h₂ hn y v)).const_mul (p y))

omit [NumberField K] in
include h₁ h₂ in
lemma integrable_massEval (hn : 2≤Fintype.card P) (q : Finset P → ℝ) :
    AverageIntegrable Z₁ Z₂ (massEval q) := by
  intro v
  exact (integrable_finsetSum (s:=Finset.univ) (fun C _ =>
      (integrable_mass_left Z₁ Z₂ h₁ hn C v).mul_const (q C))).add
    (integrable_finsetSum (s:=Finset.univ) (fun C _ =>
      (integrable_mass_right Z₁ Z₂ h₂ hn C v).mul_const (q C)))

lemma average_potentialEval (hn : 2≤Fintype.card P) (p : P → ℝ) :
    average Z₁ Z₂ h₁ h₂ (potentialEval p)=∑ y, p y*totalPotential Z₁ Z₂ h₁ h₂ y := by
  unfold potentialEval
  rw [average_sum Z₁ Z₂ h₁ h₂ _ (fun y v =>
    ((integrable_potential_left Z₁ Z₂ h₁ hn y v).add
      (integrable_potential_right Z₁ Z₂ h₂ hn y v)).const_mul (p y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [average_mul,average_add Z₁ Z₂ h₁ h₂
    (integrable_potential_left Z₁ Z₂ h₁ hn y) (integrable_potential_right Z₁ Z₂ h₂ hn y),
    average_potential_left Z₁ Z₂ h₁ h₂ hn,average_potential_right Z₁ Z₂ h₁ h₂ hn]
  rfl

lemma average_massEval (hn : 2≤Fintype.card P) (q : Finset P → ℝ) :
    average Z₁ Z₂ h₁ h₂ (massEval q)=weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) q := by
  have he : massEval q=(fun d d' => ∑ C, q C*(d.mass C+d'.mass C)) := by
    funext d d'
    simp only [massEval,weightedIntegral,mul_add,Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> ring
  rw [he,average_sum Z₁ Z₂ h₁ h₂ _ (fun C v =>
    ((integrable_mass_left Z₁ Z₂ h₁ hn C v).add
      (integrable_mass_right Z₁ Z₂ h₂ hn C v)).const_mul (q C))]
  apply Finset.sum_congr rfl
  intro C _
  rw [average_mul,average_add Z₁ Z₂ h₁ h₂
    (integrable_mass_left Z₁ Z₂ h₁ hn C) (integrable_mass_right Z₁ Z₂ h₂ hn C),
    average_mass_left Z₁ Z₂ h₁ h₂ hn,average_mass_right Z₁ Z₂ h₁ h₂ hn]
  simp only [totalMass]; ring

omit Z₁ Z₂ h₁ h₂ in
lemma massEval_edge {I : Type u6} [Fintype I] (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (d d' : Depth P) :
    massEval (SmallFiber.edgeCell w p x) d d'=
      ∑ i, w i*∑ y, p i y*(weightedOverlap d.mass (x i) y+weightedOverlap d'.mass (x i) y) := by
  have he (m : Finset P → ℝ) : weightedIntegral m (SmallFiber.edgeCell w p x)=
      ∑ i, w i*∑ y, p i y*weightedOverlap m (x i) y := by
    unfold SmallFiber.edgeCell
    rw [weighted_pair]
    unfold SmallFiber.edgeLaw
    simp only [Finset.sum_mul]
    calc
      _ = ∑ a, ∑ i, ∑ y, (if x i=a then w i*p i y else 0)*weightedOverlap m a y := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ y, (if x i=a then w i*p i y else 0)*weightedOverlap m a y := Finset.sum_comm
      _ = _ := by
        simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
        simp [Finset.mul_sum,mul_assoc]
  -- commute the source sum after inserting the indicator
  simp only [massEval,he,mul_add,Finset.sum_add_distrib]
end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u7} {I : Type u8} [Fintype P] [DecidableEq P] [Fintype I]
variable {K : Type u9} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
lemma potentialEval_mixture (w : I → ℝ) (p : I → P → ℝ) (d d' : Depth P) :
    potentialEval (fun y => ∑ i, w i*p i y) d d'=∑ i, w i*∑ y, p i y*(d.potential y+d'.potential y) := by
  simp only [potentialEval,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

lemma average_sub {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => f d d'-g d d')=
      average Z₁ Z₂ h₁ h₂ f-average Z₁ Z₂ h₁ h₂ g := by
  classical
  unfold average
  simp only [integral_sub (hi _) (hj _),mul_sub,Finset.sum_sub_distrib]
  ring

/-- The first-moment raw-depth error is archimedean only. Its global constant
is independent of the degree and all coordinates. -/
lemma arithmetic_potential_fiber_bound (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (src : I → P) (t : I → K) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)=1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hsrc : ∀ i, src i∉B i)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x)
    (ht : ∀ i y, y∈B i → (Z₁ (src i)-Z₁ y)*(Z₂ (src i)-Z₂ y)=t i) :
    (∑ y, (∑ i, w i*prob (B i) y)*totalPotential Z₁ Z₂ h₁ h₂ y) ≤
      4*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (varianceCell w B T)+
      8*overlapScale Z₁ Z₂ h₁ h₂+
      2*κ*M*potentialScale Z₁ Z₂ h₁ h₂+
      weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (SmallFiber.edgeCell w (fun i => prob (B i)) src)+16 := by
  classical
  let p : I → P → ℝ := fun i => prob (B i)
  let r : P → ℝ := fun y => ∑ i, w i*p i y
  let q := SmallFiber.edgeCell w p src
  let vcell := varianceCell w B T
  let pc := pairCell (Finset.univ : Finset P)
  let unif := prob (Finset.univ : Finset P)
  let R : Depth P → Depth P → ℝ := fun d d' =>
    4*massEval vcell d d'+8*massEval pc d d'+2*κ*M*potentialEval unif d d'+massEval q d d'
  let f : Depth P → Depth P → ℝ := fun d d' => potentialEval r d d'-R d d'
  have hp (i y) : 0≤p i y := by dsimp [p,prob]; split_ifs <;> positivity
  have hp1 (i) : ∑ y, p i y=1 := sum_prob (B i) (Finset.card_pos.mp (by have := hB i; omega))
  have hx (i) : p i (src i)=0 := by simp [p,prob,hsrc i]
  have ht' (i y) (hy : p i y≠0) : (Z₁ (src i)-Z₁ y)*(Z₂ (src i)-Z₂ y)=t i := by
    apply ht i y
    by_contra hn'; exact hy (by simp [p,prob,hn'])
  have hL := integrable_potentialEval Z₁ Z₂ h₁ h₂ hn r
  have hV := integrable_massEval Z₁ Z₂ h₁ h₂ hn vcell
  have hP := integrable_massEval Z₁ Z₂ h₁ h₂ hn pc
  have hA := integrable_potentialEval Z₁ Z₂ h₁ h₂ hn unif
  have hQ := integrable_massEval Z₁ Z₂ h₁ h₂ hn q
  have hR : AverageIntegrable Z₁ Z₂ R := fun v =>
    ((((hV v).const_mul 4).add ((hP v).const_mul 8)).add ((hA v).const_mul (2*κ*M))).add (hQ v)
  have hf : AverageIntegrable Z₁ Z₂ f := fun v => (hL v).sub (hR v)
  have hb (d d' : Depth P) (a : I → ℝ) :
      f d d'≤∑ i, w i*∑ y, p i y*|d.value (src i) y+d'.value (src i) y-a i| := by
    have hh := d.local_potential_fiber_bound d' hn w B src a T M κ hw hW.le hT hκ hB hk hsrc hdom
    rw [← potentialEval_mixture,← massEval_edge] at hh
    change potentialEval r d d'≤R d d'+_ at hh
    exact sub_le_iff_le_add'.mpr hh
  have ha (v : NumberField.InfinitePlace K) :
      (∫ ω, f (arch Z₁ v ω) (arch Z₂ v ω) ∂Grid.fullLaw)≤16 := by
    let E : Grid.FullSample → ℝ := fun ω => ∑ i, w i*∑ y, p i y*
      |(arch Z₁ v ω).value (src i) y+(arch Z₂ v ω).value (src i) y+Real.log (v (t i))|
    have hi : Integrable E Grid.fullLaw := integrable_finsetSum (s:=Finset.univ) (fun i _ =>
      (integrable_finsetSum (s:=Finset.univ) (fun y _ =>
        ((((arch_integrable Z₁ h₁ v _ _).add (arch_integrable Z₂ h₂ v _ _)).add
          (integrable_const _)).abs.const_mul (p i y)))).const_mul (w i))
    have hu : (∫ ω, E ω ∂Grid.fullLaw)≤16 := by
      simpa only [E,sub_zero,max_eq_left (abs_nonneg (_ : ℝ)),neg_zero,zero_div,Real.exp_zero,mul_one]
        using arch_weighted_defect Z₁ Z₂ h₁ h₂ v w p src t hw hW hp hp1 hx ht' 0 (by norm_num)
    exact (integral_mono (hf v) hi (fun ω => by
      simpa only [sub_neg_eq_add] using hb (arch Z₁ v ω) (arch Z₂ v ω) (fun i => -Real.log (v (t i))))).trans hu
  have hv (v : NumberField.FinitePlace K) : f (finite Z₁ h₁ v) (finite Z₂ h₂ v)≤0 := by
    have he (i y) : p i y*|(finite Z₁ h₁ v).value (src i) y+
        (finite Z₂ h₂ v).value (src i) y-(-Real.log (v (t i)))|=0 := by
      by_cases hy : p i y=0
      · simp [hy]
      · have hxy : src i≠y := by intro hh; exact hsrc i (hh ▸ (by
          by_contra hm; exact hy (by simp [p,prob,hm])))
        have hh := Arithmetic.raw_fiber_identity v.val (Z₁ (src i)-Z₁ y) (Z₂ (src i)-Z₂ y)
          (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
        rw [ht' i y hy] at hh
        change -Real.log (v (Z₁ (src i)-Z₁ y)) + -Real.log (v (Z₂ (src i)-Z₂ y)) = -Real.log (v (t i)) at hh
        simp only [finite,ite_eq_right hxy,hh,sub_self,abs_zero,mul_zero]
    simpa only [he,Finset.sum_const_zero,mul_zero] using
      hb (finite Z₁ h₁ v) (finite Z₂ h₂ v) (fun i => -Real.log (v (t i)))
  have hg : average Z₁ Z₂ h₁ h₂ f≤16 := by
    change placeAverage (placeUnion Z₁ Z₂ h₁ h₂) _ _≤16
    have hh := placeAverage_mono (placeUnion Z₁ Z₂ h₁ h₂) ha (fun v _ => hv v)
    rwa [placeAverage_arch_const] at hh
  have hRe : average Z₁ Z₂ h₁ h₂ R =
      4*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) vcell+
      8*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) pc+
      2*κ*M*(∑ y, unif y*totalPotential Z₁ Z₂ h₁ h₂ y)+
      weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) q := by
    unfold R
    rw [average_add Z₁ Z₂ h₁ h₂ (fun v => (((hV v).const_mul 4).add ((hP v).const_mul 8)).add ((hA v).const_mul (2*κ*M))) hQ,
      average_add Z₁ Z₂ h₁ h₂ (fun v => ((hV v).const_mul 4).add ((hP v).const_mul 8)) (fun v => (hA v).const_mul (2*κ*M)),
      average_add Z₁ Z₂ h₁ h₂ (fun v => (hV v).const_mul 4) (fun v => (hP v).const_mul 8)]
    simp only [average_mul,average_massEval Z₁ Z₂ h₁ h₂ hn,average_potentialEval Z₁ Z₂ h₁ h₂ hn]
  change average Z₁ Z₂ h₁ h₂ (fun d d' => potentialEval r d d'-R d d')≤16 at hg
  rw [average_sub Z₁ Z₂ h₁ h₂ hL hR,average_potentialEval Z₁ Z₂ h₁ h₂ hn,hRe] at hg
  exact sub_le_iff_le_add'.mp hg
end WeakPinned.Global

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u10} [Fintype P] [DecidableEq P]

/-- Nonnegative additive off-diagonal overlap controls the potential at every
vertex, not merely at vertices typical for the edge marginal. -/
lemma point_potential_lower (m : Finset P → ℝ) (b : ℝ) (S : P → ℝ)
    (hm : ∀ C : Finset P, (0 : ℝ) ≤ m C) (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y)
    (hn : 3≤Fintype.card P) (x : P) :
    (∑ y, prob Finset.univ y*S y)-2*weightedIntegral m (pairCell Finset.univ)≤S x := by
  let n : ℝ := Fintype.card P
  have hn3 : 3≤n := by dsimp [n]; exact_mod_cast hn
  have hn0 : n≠0 := by linarith
  let A : ℝ := (∑ y, prob Finset.univ y*S y)
  let W : ℝ := weightedIntegral m (pairCell Finset.univ)
  have hW : 0≤W := Finset.sum_nonneg (fun C _ => mul_nonneg (hm C) (pairCell_nonneg _ _))
  have hu : W=b+2*A := uniform_additive m b S hL (by omega)
  have hs : (∑ y, S y)=n*A := by
    dsimp [A,prob,n]
    simp only [Finset.mem_univ,ite_true]
    rw [← Finset.mul_sum]
    have hn0' : (Fintype.card P : ℝ) ≠ 0 := hn0
    field_simp
  have hnn : 0 ≤ ∑ y ∈ Finset.univ.erase x, (b+S x+S y) := by
    apply Finset.sum_nonneg
    intro y hy
    rw [← hL x y (Finset.ne_of_mem_erase hy).symm]
    exact Finset.sum_nonneg (fun C _ => mul_nonneg (hm C) (by dsimp; split_ifs <;> norm_num))
  have hsx : (∑ y ∈ Finset.univ.erase x, S y)=(∑ y, S y)-S x := by
    exact eq_sub_of_add_eq (Finset.sum_erase_add Finset.univ S (Finset.mem_univ x))
  have hcount : ((Finset.univ.erase x).card:ℝ)=n-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,Nat.cast_sub (by omega),Nat.cast_one]
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hcount,hsx,hs] at hnn
  change A-2*W≤S x
  nlinarith [mul_nonneg (by linarith : 0≤n-3) hW]

end WeakPinned.Variance

namespace WeakPinned
open Global Variance
open scoped BigOperators
variable {P : Type u11} {I : Type u12} [Fintype P] [Fintype I] [DecidableEq P]
variable {K : Type u13} [Field K] [NumberField K]

/-- Quantitative scale balance for arithmetic fibers, without an unboundedness assumption. -/

theorem arithmetic_scale_balance (G : Core.Fibers P I)
    (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
    (hn : 3≤Fintype.card P) (hG : 0<G.edgeCount)
    (T M κ : ℝ) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(G.targets i).card) (hk : ∀ i, 2/((G.targets i).card:ℝ)≤κ)
    (hdom : ∀ x y, G.edgeLaw x y≤M*pairProb Finset.univ x y)
    (t : I → K) (ht : ∀ i y, y∈G.targets i →
      (Z₁ (G.source i)-Z₁ y)*(Z₂ (G.source i)-Z₂ y)=t i) :
    (1-2*κ*M)*potentialScale Z₁ Z₂ h₁ h₂ ≤
      4*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (varianceCell G.fiberWeight G.targets T)+
      (10+M)*overlapScale Z₁ Z₂ h₁ h₂+16 := by
  have hn2 : 2≤Fintype.card P := by omega
  have hh := arithmetic_potential_fiber_bound Z₁ Z₂ h₁ h₂ hn2 G.fiberWeight G.targets G.source t T M κ
    G.fiberWeight_nonneg (G.sum_fiberWeight hG) hT hκ hB hk G.no_loop
    (G.fiber_domination M hdom hn2) ht
  let m := totalMass Z₁ Z₂ h₁ h₂
  let S := totalPotential Z₁ Z₂ h₁ h₂
  let r : P → ℝ := fun y => ∑ i, G.fiberWeight i*prob (G.targets i) y
  have hr0 (y) : 0≤r y := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (G.fiberWeight_nonneg i)
    unfold prob; split_ifs <;> positivity
  have hr1 : ∑ y, r y=1 := by
    dsimp [r]
    rw [Finset.sum_comm]
    have hp1 (i : I) : ∑ y, prob (G.targets i) y=1 :=
      sum_prob (G.targets i) (Finset.card_pos.mp (by have := hB i; omega))
    simp_rw [← Finset.mul_sum,hp1,mul_one]
    exact G.sum_fiberWeight hG
  have hl : potentialScale Z₁ Z₂ h₁ h₂-2*overlapScale Z₁ Z₂ h₁ h₂≤∑ y, r y*S y := by
    have hlo (y) := point_potential_lower m (baseConstant Z₁ Z₂ h₁ h₂) S
      (totalMass_nonneg Z₁ Z₂ h₁ h₂) (totalMass_overlap Z₁ Z₂ h₁ h₂ hn2) hn y
    have hu := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => mul_le_mul_of_nonneg_left (hlo y) (hr0 y))
    simpa only [← Finset.sum_mul,hr1,one_mul,potentialScale,overlapScale,m,S] using hu
  have he : SmallFiber.edgeCell G.fiberWeight (fun i => prob (G.targets i)) G.source=G.qCell := by
    funext C; exact (G.qCell_eq C).symm
  have hq : weightedIntegral m G.qCell≤M*overlapScale Z₁ Z₂ h₁ h₂ := by
    simp only [weightedIntegral,Finset.mul_sum,overlapScale]
    calc
      _ ≤ ∑ C, m C*(M*pairCell Finset.univ C) := Finset.sum_le_sum (fun C _ =>
        mul_le_mul_of_nonneg_left (G.qCell_bound hdom C) (totalMass_nonneg Z₁ Z₂ h₁ h₂ C))
      _ = _ := by apply Finset.sum_congr rfl; intro C _; dsimp [m]; ring
  rw [he] at hh
  change (∑ y, r y*S y)≤_ at hh
  change weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) G.qCell≤_ at hq
  nlinarith
end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

/-- Elementary absorption of the two asymptotically small errors. -/
lemma scale_balance_rate (W A V δ : ℕ → ℝ) (B : ℝ) (hB : 0≤B)
    (hW : ∀ j, 0≤W j) (hA : ∀ j, 0≤A j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hV : Tendsto (fun j => V j/(W j+A j+1)) atTop (𝓝 0))
    (hbal : ∀ᶠ j in atTop, (1-δ j)*A j≤4*V j+(10+B)*W j+16) :
    ∀ᶠ j in atTop, A j≤(64+4*B)*(W j+1) := by
  filter_upwards [hbal,hδ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4)),
    hV.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/16))] with j hb hd hv
  have hden : 0<W j+A j+1 := by linarith [hW j,hA j]
  have hv' := (div_lt_iff₀ hden).mp hv
  nlinarith [hW j,hA j,mul_nonneg (hW j) hB]
end WeakPinned

namespace WeakPinned
open Global Variance Filter
open scoped Topology BigOperators
variable {V : ℕ → Type u14} {I : ℕ → Type u15} {K : ℕ → Type u16} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

theorem arithmetic_scale_comparison (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y ∈ (G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    ∀ᶠ j in atTop, potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) ≤
      (64+8/θ)*(overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1) := by
  let n : ℕ → ℝ := fun j => Fintype.card (V j)
  let κ : ℕ → ℝ := fun j => 2/(n j)^γ
  have hnγ : Tendsto (fun j => (n j)^γ) atTop atTop := (tendsto_rpow_atTop hγ).comp hn
  have hκ : Tendsto κ atTop (𝓝 0) := by
    simpa only [κ,div_eq_mul_inv,mul_zero,Function.comp_def] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnγ)
  have hv := (sampling_variance_rates G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht).1
  have hs := scale_balance_rate
    (fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
    (fun j => potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
    (fiberVariance G c Z₁ Z₂ h₁ h₂) (fun j => 2*κ j*(2/θ)) (2/θ) (by positivity)
    (fun j => overlapScale_nonneg _ _ _ _) (fun j => potentialScale_nonneg _ _ _ _)
    (by simpa using (tendsto_const_nhds.mul hκ).mul_const (2/θ)) hv
  have hb : ∀ᶠ j in atTop,
      (1-2*κ j*(2/θ))*potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) ≤
      4*fiberVariance G c Z₁ Z₂ h₁ h₂ j+(10+2/θ)*overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+16 := by
    filter_upwards [hn.eventually (eventually_ge_atTop (3:ℝ)),hnγ.eventually (eventually_ge_atTop (2:ℝ))] with j hj hjγ
    have hn3 : 3≤Fintype.card (V j) := by exact_mod_cast hj
    have hne : 0<(G j).edgeCount := (hG j).edgeCount_pos (by linarith [hηb j])
    have hn0 : 0<n j := by change (0:ℝ)<Fintype.card (V j); linarith
    have hBk (i) : (n j)^γ≤((G j).targets i).card := (hG j).fiber i |>.le
    have hBk2 (i) : 2≤((G j).targets i).card := by exact_mod_cast hjγ.trans (hBk i)
    have hk (i) : 2/(((G j).targets i).card:ℝ)≤κ j :=
      div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hn0 _) (hBk i)
    have hT : 1≤(n j)^(1-c) := Real.one_le_rpow (by linarith) (by linarith)
    exact arithmetic_scale_balance (G j) (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) hn3 hne
      ((n j)^(1-c)) (2/θ) (κ j) hT (by dsimp [κ]; positivity) hBk2 hk
      ((hG j).uniform_domination hθ (hηb j)) (t j) (ht j)
  have hh := hs hb
  convert hh using 1; ring_nf
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
