import Mathlib
import OAI.Probability.Contingency.ChildLogConcavity
import OAI.Probability.Contingency.SafeBins

namespace OAI

/-! Accepted Chain. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.FiniteChain
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

 

structure AcceptedData (V : Type*) [Fintype V] where
  f : V → ℝ
  fpos : ∀ x, 0<f x
  count : V → V → ℝ
  nonneg : ∀ x y, 0≤count x y
  symmetric : ∀ x y, count x y=count y x
  diagonal : ∀ x, count x x=0
  q : ℝ
  qpos : 0≤q
  hold : ∀ x, q*(∑ y,count x y)≤f x/2

namespace AcceptedData
variable (A : AcceptedData V)

def total : ℝ := ∑ x,A.f x

omit [DecidableEq V] in
theorem total_pos : 0<A.total := by
  unfold total
  exact Finset.sum_pos (fun x _ => A.fpos x) Finset.univ_nonempty

def rate (x y : V) : ℝ := A.q*A.count x y/A.f x

def kernel (x y : V) : ℝ := if x=y then 1-∑ z,A.rate x z else A.rate x y

omit [DecidableEq V] [Nonempty V] in
theorem rate_nonneg (x y : V) : 0≤A.rate x y :=
  div_nonneg (mul_nonneg A.qpos (A.nonneg x y)) (A.fpos x).le

omit [DecidableEq V] [Nonempty V] in
theorem rate_sum (x : V) : (∑ y,A.rate x y)≤1/2 := by
  simp only [rate,← Finset.sum_div,← Finset.mul_sum]
  apply (div_le_iff₀ (A.fpos x)).mpr
  have := A.hold x
  linarith

omit [DecidableEq V] [Nonempty V] in
@[simp] theorem rate_self (x : V) : A.rate x x=0 := by simp [rate,A.diagonal]

def chain : Chain V where
  π := fun x => A.f x/A.total
  P := A.kernel
  positive := fun x => div_pos (A.fpos x) A.total_pos
  normalized := by simp only [← Finset.sum_div]; exact div_self A.total_pos.ne'
  nonneg := by
    intro x y
    by_cases h : x=y
    · subst y; simp only [kernel,ite_true]
      linarith [A.rate_sum x]
    · simp only [kernel,ite_eq_right h]; exact A.rate_nonneg x y
  stochastic := by
    intro x
    have he : (∑ y,A.kernel x y)=1-∑ y,A.rate x y+∑ y,A.rate x y := by
      calc
        _ = ∑ y, ((if x=y then 1-∑ z,A.rate x z else 0)+A.rate x y) := by
          apply Finset.sum_congr rfl; intro y _
          by_cases h : x=y
          · subst y; simp [kernel]
          · simp [kernel,h]
        _ = _ := by simp [Finset.sum_add_distrib]
    rw [he]; ring
  reversible := by
    intro x y
    by_cases h : x=y
    · subst y; rfl
    · simp only [kernel,ite_eq_right h,ite_eq_right (Ne.symm h),rate]
      rw [A.symmetric]
      field_simp [A.total_pos.ne',(A.fpos x).ne',(A.fpos y).ne']
  lazy := by
    intro x
    simp only [kernel,ite_true]
    linarith [A.rate_sum x]

@[simp] theorem chain_pi (x : V) : A.chain.π x=A.f x/A.total := rfl
@[simp] theorem chain_P (x y : V) : A.chain.P x y=A.kernel x y := rfl

theorem offdiagonal_flow (x y : V) (h : x≠y) :
    A.chain.π x*A.chain.P x y=A.q*A.count x y/A.total := by
  simp only [chain_pi,chain_P,kernel,ite_eq_right h,rate]
  field_simp [(A.fpos x).ne']

theorem energy_formula (H : V → ℝ) :
    A.chain.energy H = (A.q/A.total)*(∑ x,∑ y,A.count x y*(H x-H y)^2)/2 := by
  unfold Chain.energy
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro y _
  by_cases h : x=y
  · subst y; simp
  · rw [A.offdiagonal_flow x y h]; ring

 

theorem variance_formula (H : V → ℝ) :
    A.chain.variance H = weightedVariance A.f H/A.total := by
  unfold Chain.variance Chain.mean weightedVariance
  simp only [chain_pi]
  have he : (∑ x,A.f x/A.total*H x)=(∑ x,A.f x*H x)/A.total := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro x _; ring
  rw [he]
  simp only [weightedMean,totalWeight,total,Finset.sum_div]
  apply Finset.sum_congr rfl; intro x _
  ring

end AcceptedData
end
end Contingency.FiniteChain

 

 

open scoped BigOperators
namespace Contingency.FiniteChain.Chain
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] (C : Chain V)

def mass (A : Finset V) : ℝ := ∑ x ∈ A, C.π x
def cut (A : Finset V) : ℝ := ∑ x, ∑ y,
  if x∈A ∧ y∉A then C.π x*C.P x y else 0
def variationEnergy (f : V → ℝ) : ℝ :=
  (∑ x, ∑ y, C.π x*C.P x y*|f x-f y|)/2

def positiveSupport (f : V → ℝ) : Finset V := Finset.univ.filter fun x => 0<f x

omit [DecidableEq V] in
theorem mass_mono {A B : Finset V} (h : A⊆B) : C.mass A≤C.mass B :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun x _ _ => (C.positive x).le)

omit [DecidableEq V] in
theorem mass_nonneg (A : Finset V) : 0≤C.mass A :=
  Finset.sum_nonneg fun x _ => (C.positive x).le

omit [DecidableEq V] in
theorem mass_le_one (A : Finset V) : C.mass A≤1 := by
  have h := C.mass_mono (Finset.subset_univ A)
  simpa only [mass,C.normalized] using h

theorem cut_as_restricted (A : Finset V) :
    C.cut A=∑ x∈A, ∑ y∈Finset.univ\A, C.π x*C.P x y := by
  have hn : Finset.univ.filter (fun x : V => x∉A)=Finset.univ\A := by ext; simp
  simp only [cut,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero,← Finset.sum_filter]
  rw [hn]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem indicator_energy (A : Finset V) :
    C.variationEnergy (fun x => if x∈A then 1 else 0)=C.cut A := by
  have he (x y : V) :
      C.π x*C.P x y*|(if x∈A then 1 else 0)-(if y∈A then 1 else 0)| =
      (if x∈A ∧ y∉A then C.π x*C.P x y else 0)+
      (if y∈A ∧ x∉A then C.π y*C.P y x else 0) := by
    by_cases hx : x∈A <;> by_cases hy : y∈A <;> simp [hx,hy,C.reversible]
  have hs : (∑ x, ∑ y, if y∈A ∧ x∉A then C.π y*C.P y x else 0)=C.cut A := by
    rw [Finset.sum_comm]; rfl
  simp only [variationEnergy,he,Finset.sum_add_distrib]
  rw [hs]
  change (C.cut A+C.cut A)/2=C.cut A
  ring

 

theorem coarea (κ : ℝ)
    (hcut : ∀ A : Finset V, κ*min (C.mass A) (1-C.mass A)≤C.cut A)
    (f : V → ℝ) (hf : ∀ x, 0≤f x) (hs : C.mass (positiveSupport f)≤1/2) :
    κ*C.mean f≤C.variationEnergy f := by
  generalize hn : (positiveSupport f).card=n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hz : positiveSupport f=∅
    · have hf0 : ∀ x, f x=0 := by
        intro x
        have hh : ¬0<f x := by
          intro h
          have hm : x∈positiveSupport f := by simp [positiveSupport,h]
          rw [hz] at hm; simp at hm
        exact le_antisymm (le_of_not_gt hh) (hf x)
      simp [mean,variationEnergy,hf0]
    · have hS : (positiveSupport f).Nonempty := Finset.nonempty_iff_ne_empty.mpr hz
      obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image (positiveSupport f) f hS
      have hx0 : 0<f x := by simpa [positiveSupport] using hx
      let δ := f x
      let g := fun y => if 0<f y then f y-δ else 0
      have hδ : 0<δ := hx0
      have hlow (y : V) (hy : 0<f y) : δ≤f y :=
        hmin y (by simp [positiveSupport,hy])
      have hg : ∀ y, 0≤g y := by
        intro y
        by_cases hy : 0<f y
        · simp only [g,ite_eq_left hy]; exact sub_nonneg.mpr (hlow y hy)
        · simp [g,hy]
      have hsub : positiveSupport g⊆positiveSupport f := by
        intro y hy
        simp only [positiveSupport,Finset.mem_filter,Finset.mem_univ,true_and] at hy ⊢
        by_contra hf'
        simp [g,hf'] at hy
      have hxg : x∉positiveSupport g := by simp [positiveSupport,g,hx0,δ]
      have hlt : (positiveSupport g).card<n := by
        rw [← hn]
        apply Finset.card_lt_card
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun he => hxg (he.symm ▸ hx)⟩
      have hgS : C.mass (positiveSupport g)≤1/2 := (C.mass_mono hsub).trans hs
      have hi := ih _ hlt g hg hgS rfl
      have hc : κ*C.mass (positiveSupport f)≤C.cut (positiveSupport f) := by
        have hh := hcut (positiveSupport f)
        rwa [min_eq_left (by linarith)] at hh
      have decomp (y : V) : f y=δ*(if y∈positiveSupport f then 1 else 0)+g y := by
        by_cases hy : 0<f y
        · simp [positiveSupport,g,hy]
        · have hf0 : f y=0 := le_antisymm (le_of_not_gt hy) (hf y)
          simp [positiveSupport,g,hf0]
      have hm : C.mean f=δ*C.mass (positiveSupport f)+C.mean g := by
        unfold mean mass
        simp_rw [decomp]
        simp only [mul_add,Finset.sum_add_distrib]
        congr 1
        simp only [mul_ite,mul_one,mul_zero,← Finset.sum_filter]
        rw [Finset.filter_mem_eq_inter,Finset.univ_inter]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _; ring
      have he (y z : V) : |f y-f z| =
          δ*|(if y∈positiveSupport f then 1 else 0)-(if z∈positiveSupport f then 1 else 0)|+
          |g y-g z| := by
        by_cases hy : 0<f y <;> by_cases hz : 0<f z
        · simp [positiveSupport,g,hy,hz,show f y-δ-(f z-δ)=f y-f z by ring]
        · have hz0 : f z=0 := le_antisymm (le_of_not_gt hz) (hf z)
          simp [positiveSupport,g,hy,hz0,abs_of_nonneg (hf y),abs_of_nonneg (sub_nonneg.mpr (hlow y hy))]
        · have hy0 : f y=0 := le_antisymm (le_of_not_gt hy) (hf y)
          simp [positiveSupport,g,hz,hy0,abs_of_nonneg (hf z),abs_of_nonpos (sub_nonpos.mpr (hlow z hz))]
        · simp [positiveSupport,g,
            show f y=0 from le_antisymm (le_of_not_gt hy) (hf y),
            show f z=0 from le_antisymm (le_of_not_gt hz) (hf z)]
      have heq : C.variationEnergy f=δ*C.cut (positiveSupport f)+C.variationEnergy g := by
        rw [← C.indicator_energy]
        simp only [variationEnergy,he,mul_add,Finset.sum_add_distrib]
        have ht : (∑ y, ∑ z, C.π y*C.P y z*(δ*|(if y∈positiveSupport f then 1 else 0)-
            (if z∈positiveSupport f then 1 else 0)|)) =
            δ*(∑ y, ∑ z, C.π y*C.P y z*|(if y∈positiveSupport f then 1 else 0)-
            (if z∈positiveSupport f then 1 else 0)|) := by
          simp only [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro y _
          apply Finset.sum_congr rfl; intro z _; ring
        rw [ht]; ring
      rw [hm,heq]
      have hh := mul_le_mul_of_nonneg_left hc hδ.le
      nlinarith only [hh,hi]

end
end Contingency.FiniteChain.Chain

 

 

open scoped BigOperators
namespace Contingency.FiniteChain.Chain
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] (C : Chain V)

omit [DecidableEq V] in
theorem variation_square_cauchy (g : V → ℝ) :
    (C.variationEnergy (fun x => g x^2))^2 ≤ 2*C.energy g*C.normSq g := by
  have hc : (∑ xy : V×V, C.π xy.1*C.P xy.1 xy.2*|g xy.1^2-g xy.2^2|)^2 ≤
      (∑ xy : V×V, C.π xy.1*C.P xy.1 xy.2*(g xy.1-g xy.2)^2)*
      (∑ xy : V×V, C.π xy.1*C.P xy.1 xy.2*(g xy.1+g xy.2)^2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro xy _; exact mul_nonneg (mul_nonneg (C.positive _).le (C.nonneg _ _)) (sq_nonneg _)
    · intro xy _; exact mul_nonneg (mul_nonneg (C.positive _).le (C.nonneg _ _)) (sq_nonneg _)
    · intro xy _; rw [mul_pow,sq_abs]; nlinarith only []
  have hp : (∑ x, ∑ y, C.π x*C.P x y*(g x+g y)^2)≤4*C.normSq g := by
    calc
      _ ≤ ∑ x, ∑ y, (2*(C.π x*C.P x y*g x^2)+2*(C.π x*C.P x y*g y^2)) := by
        apply Finset.sum_le_sum; intro x _
        apply Finset.sum_le_sum; intro y _
        have hh : (g x+g y)^2≤2*g x^2+2*g y^2 := by nlinarith [sq_nonneg (g x-g y)]
        have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg (C.positive x).le (C.nonneg x y))
        nlinarith only [hm]
      _ = _ := by
        simp only [Finset.sum_add_distrib,← Finset.mul_sum]
        rw [C.edge_sums_left,C.edge_sums_right]; ring
  have he : 0≤C.energy g := by
    unfold energy
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (C.positive x).le (C.nonneg x y)) (sq_nonneg _)
  simp only [Fintype.sum_prod_type] at hc
  have hh := mul_le_mul_of_nonneg_left hp he
  unfold variationEnergy energy at *
  nlinarith only [hc,hh]

theorem small_support_poincare (κ : ℝ) (hκ : 0<κ)
    (hcut : ∀ A : Finset V, κ*min (C.mass A) (1-C.mass A)≤C.cut A)
    (g : V → ℝ) (hg : ∀ x, 0≤g x) (hs : C.mass (positiveSupport g)≤1/2) :
    C.normSq g ≤ (2/κ^2)*C.energy g := by
  have hs' : positiveSupport (fun x => g x^2)=positiveSupport g := by
    ext x
    simp only [positiveSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h; exact lt_of_le_of_ne (hg x) (Ne.symm (sq_pos_iff.mp h))
    · intro h; exact sq_pos_of_pos h
  have hc := C.coarea κ hcut (fun x => g x^2) (fun x => sq_nonneg _) (hs' ▸ hs)
  change κ*C.normSq g ≤ _ at hc
  have hv : 0≤C.variationEnergy (fun x => g x^2) := by
    unfold variationEnergy
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (C.positive x).le (C.nonneg x y)) (abs_nonneg _)
  have hh := (sq_le_sq₀ (mul_nonneg hκ.le (C.normSq_nonneg g)) hv).mpr hc
  have hcs := C.variation_square_cauchy g
  by_cases hz : C.normSq g=0
  · rw [hz]
    apply mul_nonneg (by positivity)
    unfold energy
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (C.positive x).le (C.nonneg x y)) (sq_nonneg _)
  · have hn : 0<C.normSq g := lt_of_le_of_ne (C.normSq_nonneg g) (Ne.symm hz)
    have hab : κ^2*C.normSq g≤2*C.energy g := by nlinarith only [hh,hcs,hn]
    have hd : 0<κ^2 := sq_pos_of_pos hκ
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hd).mpr
    nlinarith only [hab]

 

omit [DecidableEq V] in
theorem median_exists (f : V → ℝ) : ∃ a : ℝ,
    C.mass (Finset.univ.filter fun x => a<f x)≤1/2 ∧
    C.mass (Finset.univ.filter fun x => f x<a)≤1/2 := by
  classical
  have hV : (Finset.univ : Finset V).Nonempty := by
    by_contra h
    have he : (Finset.univ : Finset V)=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hn := C.normalized
    rw [he,Finset.sum_empty] at hn
    norm_num at hn
  let A : Finset V := Finset.univ.filter fun x => 1/2≤C.mass (Finset.univ.filter fun y => f y≤f x)
  have hA : A.Nonempty := by
    obtain ⟨x,hx,hmax⟩ := Finset.exists_max_image Finset.univ f hV
    refine ⟨x,?_⟩
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    have he : Finset.univ.filter (fun y => f y≤f x)=Finset.univ := by
      ext y; simp [hmax y (Finset.mem_univ y)]
    rw [he,mass,C.normalized]
    norm_num
  obtain ⟨x,hx,hmin⟩ := Finset.exists_min_image A f hA
  have hmed : 1/2≤C.mass (Finset.univ.filter fun y => f y≤f x) := by simpa [A] using hx
  refine ⟨f x,?_,?_⟩
  · have he : C.mass (Finset.univ.filter fun y => f x<f y)+
        C.mass (Finset.univ.filter fun y => f y≤f x)=1 := by
      simp only [mass,Finset.sum_filter,← Finset.sum_add_distrib]
      calc
        _ = ∑ y, C.π y := by
          apply Finset.sum_congr rfl; intro y _
          by_cases h : f x<f y
          · simp [h,not_le.mpr h]
          · simp [h,le_of_not_gt h]
        _ = 1 := C.normalized
    linarith
  · by_contra hh
    have hl : 1/2<C.mass (Finset.univ.filter fun y => f y<f x) := lt_of_not_ge hh
    let D := Finset.univ.filter fun y => f y<f x
    have hD : D.Nonempty := by
      by_contra h
      have he : D=∅ := Finset.not_nonempty_iff_eq_empty.mp h
      change 1/2<C.mass D at hl
      rw [he,mass,Finset.sum_empty] at hl
      norm_num at hl
    obtain ⟨z,hz,hmax⟩ := Finset.exists_max_image D f hD
    have hzlt : f z<f x := by simpa [D] using hz
    have hsub : D⊆Finset.univ.filter (fun y => f y≤f z) := by
      intro y hy
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact hmax y hy
    have hzA : z∈A := by
      simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
      exact hl.le.trans (C.mass_mono hsub)
    exact (not_le.mpr hzlt) (hmin z hzA)

omit [DecidableEq V] in
theorem variance_le_constant (f : V → ℝ) (a : ℝ) :
    C.variance f≤∑ x, C.π x*(f x-a)^2 := by
  have hm : (∑ x, C.π x*(f x-C.mean f))=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,C.normalized,one_mul]
    change C.mean f-C.mean f=0
    ring
  have he (x : V) : C.π x*(f x-a)^2 =
      C.π x*(f x-C.mean f)^2 + 2*(C.mean f-a)*(C.π x*(f x-C.mean f)) +
      (C.mean f-a)^2*C.π x := by ring
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,hm,C.normalized,mul_zero,add_zero,mul_one]
  change C.variance f≤C.variance f+(C.mean f-a)^2
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem positive_negative_squares (u : ℝ) : (max u 0)^2+(max (-u) 0)^2=u^2 := by
  by_cases h : 0≤u
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]; ring
  · rw [max_eq_right (le_of_not_ge h),max_eq_left (by linarith)]; ring

theorem positive_negative_edge (u v : ℝ) :
    (max u 0-max v 0)^2+(max (-u) 0-max (-v) 0)^2≤(u-v)^2 := by
  by_cases hu : 0≤u <;> by_cases hv : 0≤v
  · rw [max_eq_left hu,max_eq_left hv,max_eq_right (neg_nonpos.mpr hu),max_eq_right (neg_nonpos.mpr hv)]
    simp
  · have hv' : v≤0 := le_of_not_ge hv
    rw [max_eq_left hu,max_eq_right hv',max_eq_right (neg_nonpos.mpr hu),max_eq_left (neg_nonneg.mpr hv')]
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hu hv']
  · have hu' : u≤0 := le_of_not_ge hu
    rw [max_eq_right hu',max_eq_left hv,max_eq_left (neg_nonneg.mpr hu'),max_eq_right (neg_nonpos.mpr hv)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hu' hv]
  · have hu' : u≤0 := le_of_not_ge hu
    have hv' : v≤0 := le_of_not_ge hv
    rw [max_eq_right hu',max_eq_right hv',max_eq_left (neg_nonneg.mpr hu'),max_eq_left (neg_nonneg.mpr hv')]
    nlinarith

 
theorem cheeger_poincare (κ : ℝ) (hκ : 0<κ)
    (hcut : ∀ A : Finset V, κ*min (C.mass A) (1-C.mass A)≤C.cut A)
    (f : V → ℝ) : C.variance f≤(2/κ^2)*C.energy f := by
  obtain ⟨a,hupper,hlower⟩ := C.median_exists f
  let g := fun x => max (f x-a) 0
  let h := fun x => max (a-f x) 0
  have hgS : positiveSupport g=Finset.univ.filter (fun x => a<f x) := by
    ext x
    simp only [positiveSupport,Finset.mem_filter,Finset.mem_univ,true_and,g,lt_max_iff,lt_self_iff_false,or_false,sub_pos]
  have hhS : positiveSupport h=Finset.univ.filter (fun x => f x<a) := by
    ext x
    simp only [positiveSupport,Finset.mem_filter,Finset.mem_univ,true_and,h,lt_max_iff,lt_self_iff_false,or_false,sub_pos]
  have hg := C.small_support_poincare κ hκ hcut g (fun x => le_max_right _ _) (by rw [hgS]; exact hupper)
  have hh := C.small_support_poincare κ hκ hcut h (fun x => le_max_right _ _) (by rw [hhS]; exact hlower)
  have hs : C.normSq g+C.normSq h=∑ x, C.π x*(f x-a)^2 := by
    simp only [normSq,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    have he := positive_negative_squares (f x-a)
    have he' : (g x)^2+(h x)^2=(f x-a)^2 := by
      simpa only [g,h,neg_sub] using he
    nlinarith only [congrArg (fun z => C.π x*z) he']
  have he : C.energy g+C.energy h≤C.energy f := by
    unfold energy
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro y _
    have he := positive_negative_edge (f x-a) (f y-a)
    have he' : (g x-g y)^2+(h x-h y)^2≤(f x-f y)^2 := by
      simpa only [g,h,neg_sub,sub_sub_sub_cancel_right] using he
    have hm := mul_le_mul_of_nonneg_left he' (mul_nonneg (C.positive x).le (C.nonneg x y))
    nlinarith only [hm]
  have hv := C.variance_le_constant f a
  rw [← hs] at hv
  have he' := mul_le_mul_of_nonneg_left he (show 0≤2/κ^2 by positivity)
  nlinarith only [hg,hh,hv,he']

end
end Contingency.FiniteChain.Chain

 

 

open scoped BigOperators
namespace Contingency.Grid
noncomputable section
variable {q K : ℕ}
open Contingency.FiniteChain

def Adj (v w : Vertex q K) : Prop := ∃ i,neighbors (corner v) (corner w) i

theorem adj_symm (v w : Vertex q K) : Adj v w ↔ Adj w v := by
  constructor <;> rintro ⟨i,hi⟩ <;> exact ⟨i,neighbors_symm _ _ _ hi⟩

theorem adj_irrefl (v : Vertex q K) : ¬Adj v v := by
  rintro ⟨i,hi⟩
  rcases hi.1 with h | h <;> omega

def axis {v : Vertex q K} (w : {w : Vertex q K // Adj v w}) : Fin q := w.property.choose

theorem axis_spec {v : Vertex q K} (w : {w : Vertex q K // Adj v w}) :
    neighbors (corner v) (corner w.val) (axis w) := w.property.choose_spec

def signedAxis {v : Vertex q K} (w : {w : Vertex q K // Adj v w}) : Fin q×Bool := by
  classical
  exact (axis w,decide ((v (axis w)).val+1=(w.val (axis w)).val))

theorem signedAxis_injective (v : Vertex q K) : Function.Injective (@signedAxis q K v) := by
  classical
  intro w z h
  have ha : axis w=axis z := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  simp only [signedAxis] at hb
  have hw := axis_spec w
  have hz := axis_spec z
  rw [← ha] at hb hz
  apply Subtype.ext
  funext j
  apply Fin.ext
  by_cases hj : j=axis w
  · subst j
    have hw' := hw.1
    have hz' := hz.1
    dsimp [corner] at hw' hz'
    by_cases hw0 : (v (axis w)).val+1=(w.val (axis w)).val <;>
      by_cases hz0 : (v (axis w)).val+1=(z.val (axis w)).val <;>
      simp [hw0,hz0] at hb <;> omega
  · exact (hw.2 j hj).symm.trans (hz.2 j hj)

theorem neighbor_card (v : Vertex q K) : Nat.card {w : Vertex q K // Adj v w} ≤ 2*q := by
  classical
  let := Fintype.ofFinite {w : Vertex q K // Adj v w}
  have h := Fintype.card_le_of_injective (@signedAxis q K v) (signedAxis_injective v)
  simpa [Nat.card_eq_fintype_card,Nat.mul_comm] using h

def edgeWeight (W : Vertex q K → ℝ) (v w : Vertex q K) : ℝ := by
  classical
  exact if Adj v w then min (W v) (W w) else 0

theorem edgeWeight_nonneg (W : Vertex q K → ℝ) (hW : ∀ v,0<W v) (v w) : 0 ≤ edgeWeight W v w := by
  classical
  unfold edgeWeight
  split_ifs
  · exact le_min (hW v).le (hW w).le
  · rfl

theorem edgeWeight_sum (W : Vertex q K → ℝ) (hW : ∀ v,0<W v) (v) :
    (∑ w,edgeWeight W v w) ≤ 2*q*W v := by
  classical
  let : Fintype {w : Vertex q K // Adj v w} := Fintype.ofFinite _
  calc
    _ ≤ ∑ w : Vertex q K,if Adj v w then W v else 0 := by
      apply Finset.sum_le_sum; intro w _
      unfold edgeWeight
      split_ifs
      · exact min_le_left _ _
      · rfl
    _ = (Nat.card {w : Vertex q K // Adj v w}:ℝ)*W v := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_subtype (F:=inferInstance) (p:=fun w => Adj v w) _ (by intro w; simp)]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ _ := by
      have hh : (Nat.card {w : Vertex q K // Adj v w}:ℝ)≤2*q := by exact_mod_cast neighbor_card v
      exact mul_le_mul_of_nonneg_right hh (hW v).le

 
def metropolis [Nonempty (Vertex q K)] (W : Vertex q K → ℝ) (hW : ∀ v,0<W v)
    (p d : ℝ) (hd : 0<d) (hq : (q:ℝ) ≤ d) (hp0 : 0 ≤ p) (hp : p ≤ 1/(8*d)) : AcceptedData (Vertex q K) where
  f := W
  fpos := hW
  count := edgeWeight W
  nonneg := edgeWeight_nonneg W hW
  symmetric := by
    intro v w
    classical
    simp only [edgeWeight,adj_symm v w,min_comm]
  diagonal := by
    intro v
    classical
    simp only [edgeWeight,ite_eq_right (adj_irrefl v)]
  q := p
  qpos := hp0
  hold := by
    intro v
    have hh := mul_le_mul_of_nonneg_left (edgeWeight_sum W hW v) hp0
    have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
    have hpq : p*(2*q) ≤ 1/4 := by
      calc
        _ ≤ (1/(8*d))*(2*q) := mul_le_mul_of_nonneg_right hp (by positivity)
        _ ≤ (1/(8*d))*(2*d) := by gcongr
        _ = 1/4 := by field_simp; ring
    have hw := mul_le_mul_of_nonneg_right hpq (hW v).le
    nlinarith only [hh,hw,hW v]

theorem border_sum (W : Vertex q K → ℝ) (A : Finset (Vertex q K)) :
    border A W=∑ v,∑ w,if v∈A ∧ w∉A then edgeWeight W v w else 0 := by
  classical
  have hh : border A W=∑ vw : Vertex q K×Vertex q K,
      if vw.1∈A ∧ vw.2∉A ∧ Adj vw.1 vw.2 then min (W vw.1) (W vw.2) else 0 := by
    rw [← Finset.sum_filter]
    change (∑ e : Cut A,min (W e.val.1) (W e.val.2))=_
    symm
    exact Finset.sum_subtype (F:=cutFintype A)
      (Finset.univ.filter fun vw : Vertex q K×Vertex q K => vw.1∈A ∧ vw.2∉A ∧ Adj vw.1 vw.2)
      (by intro vw; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; rfl)
      (fun vw => min (W vw.1) (W vw.2))
  rw [hh,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro v _
  apply Finset.sum_congr rfl; intro w _
  unfold edgeWeight
  by_cases h1 : v∈A <;> by_cases h2 : w∈A <;> by_cases h3 : Adj v w <;> simp [h1,h2,h3]

theorem metropolis_cut [Nonempty (Vertex q K)] (W : Vertex q K → ℝ) (hW : ∀ v,0<W v)
    (p d : ℝ) (hd : 0<d) (hq : (q:ℝ) ≤ d) (hp0 : 0 ≤ p) (hp : p ≤ 1/(8*d))
    (A : Finset (Vertex q K)) : (metropolis W hW p d hd hq hp0 hp).chain.cut A=
      p/(∑ v,W v)*border A W := by
  classical
  let M := metropolis W hW p d hd hq hp0 hp
  rw [border_sum,Finset.mul_sum]
  unfold Chain.cut
  apply Finset.sum_congr rfl; intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w _
  by_cases hh : v∈A ∧ w∉A
  · rw [ite_eq_left hh,ite_eq_left hh]
    have hne : v≠w := by intro he; exact hh.2 (he ▸ hh.1)
    rw [M.offdiagonal_flow v w hne]
    change p*edgeWeight W v w/(∑ v,W v)=p/(∑ v,W v)*edgeWeight W v w
    ring
  · rw [ite_eq_right hh,ite_eq_right hh,mul_zero]

end
end Contingency.Grid

 

 

open scoped BigOperators
namespace Contingency.Dense.BinProblem
noncomputable section
open Contingency.Grid Contingency.FiniteChain
variable {a c q K : ℕ} (D : BinProblem a c q K)

def chain (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/(8*D.d)) : Chain (Vertex q K) := by
  letI : Nonempty (Vertex q K) := ⟨fun _ => ⟨0,D.Kpos⟩⟩
  exact (metropolis D.weight D.weight_pos p D.d (by linarith [D.hd]) D.hq hp0 hp).chain

theorem chain_mass (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/(8*D.d)) (V : Finset (Vertex q K)) :
    (D.chain p hp0 hp).mass V=(∑ v∈V,D.weight v)/D.Z := by
  simp only [Chain.mass,chain,AcceptedData.chain,metropolis,AcceptedData.total, Z,Finset.sum_div]

theorem chain_cut (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/(8*D.d)) (V : Finset (Vertex q K)) :
    (D.chain p hp0 hp).cut V=p/D.Z*border V D.weight := by
  let : Nonempty (Vertex q K) := ⟨fun _ => ⟨0,D.Kpos⟩⟩
  exact metropolis_cut D.weight D.weight_pos p D.d _ D.hq hp0 hp V

def kappa : ℝ := 1/(100000*D.d^2*K)

theorem kappa_pos : 0<D.kappa := by
  have hd : 0<D.d := by linarith [D.hd]
  have hk : (0:ℝ)<K := by exact_mod_cast D.Kpos
  unfold kappa
  positivity

theorem weighted_compl (V : Finset (Vertex q K)) :
    (∑ v∈Vᶜ,D.weight v)=D.Z-∑ v∈V,D.weight v := by
  have hh := Finset.sum_add_sum_compl V D.weight
  change _=D.Z at hh
  linarith

theorem chain_conductance (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/(8*D.d))
    (hplo : 1/(16*D.d) ≤ p) (V : Finset (Vertex q K)) :
    D.kappa*min ((D.chain p hp0 hp).mass V) (1-(D.chain p hp0 hp).mass V) ≤
      (D.chain p hp0 hp).cut V := by
  classical
  rw [D.chain_mass,D.chain_cut]
  have hc : 1-(∑ v∈V,D.weight v)/D.Z=(∑ v∈Vᶜ,D.weight v)/D.Z := by
    rw [D.weighted_compl]
    field_simp [D.Zpos.ne']
  rw [hc,min_div_div_right D.Zpos.le]
  by_cases hV : V.Nonempty
  · by_cases hVc : Vᶜ.Nonempty
    · have hh := bin_conductance_numerator D.e _ _ D.widths D.d (by linarith [D.hd]) D.dim D.hq
        (by have := D.Kpos; omega) (fun i => by exact_mod_cast D.hR i)
        (fun j => by exact_mod_cast D.hP j) (fun i => by exact_mod_cast D.hRmax i)
        (fun j => by exact_mod_cast D.hPmax j) (fun i j => by exact Nat.cast_nonneg _)
        D.widthhi p hplo V hV hVc
      have hh' := (div_le_div_iff_of_pos_right D.Zpos).mpr hh
      change D.kappa*min (∑ v∈V,D.weight v) (∑ v∈Vᶜ,D.weight v)/D.Z ≤ p*border V D.weight/D.Z at hh'
      convert hh' using 1 <;> ring
    · have he : Vᶜ=∅ := Finset.not_nonempty_iff_eq_empty.mp hVc
      have hzero : min (∑ v∈V,D.weight v) (∑ v∈Vᶜ,D.weight v)=0 := by
        rw [he,Finset.sum_empty,min_eq_right (Finset.sum_nonneg fun v _ => (D.weight_pos v).le)]
      rw [hzero,zero_div,mul_zero]
      apply mul_nonneg (div_nonneg hp0 D.Zpos.le)
      unfold border
      exact Finset.sum_nonneg fun e _ => le_min (D.weight_pos _).le (D.weight_pos _).le
  · have he : V=∅ := Finset.not_nonempty_iff_eq_empty.mp hV
    have hzero : min (∑ v∈V,D.weight v) (∑ v∈Vᶜ,D.weight v)=0 := by
      rw [he,Finset.sum_empty,min_eq_left (Finset.sum_nonneg fun v _ => (D.weight_pos v).le)]
    rw [hzero,zero_div,mul_zero]
    apply mul_nonneg (div_nonneg hp0 D.Zpos.le)
    unfold border
    exact Finset.sum_nonneg fun e _ => le_min (D.weight_pos _).le (D.weight_pos _).le

theorem chain_poincare (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/(8*D.d))
    (hplo : 1/(16*D.d) ≤ p) (f : Vertex q K → ℝ) :
    (D.chain p hp0 hp).variance f ≤ (2/D.kappa^2)*(D.chain p hp0 hp).energy f := by
  apply (D.chain p hp0 hp).cheeger_poincare D.kappa D.kappa_pos
  exact D.chain_conductance p hp0 hp hplo

end
end Contingency.Dense.BinProblem

end

end OAI
