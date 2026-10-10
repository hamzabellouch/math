import Mathlib
import OAI.Analysis.PathSelection.ClockExpansions

namespace OAI

/-! Multiplication, word polynomials, exponential decay and geometric inverses. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem SectorExpansion.mul {f g : ℂ → ℂ} {E F : Set ℝ} {b c : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) (hg : SectorExpansion g F c)
    (hb : ∀ β ∈ E, SectorSlow (b β)) (hc : ∀ γ ∈ F, SectorSlow (c γ)) :
    SectorExpansion (fun z => f z*g z) (exponentSum E F)
      (exponentConvolution hf.bounded_above hg.bounded_above hf.finite_above hg.finite_above b c) := by
  classical
  obtain ⟨A,hA⟩ := hf.bounded_above
  obtain ⟨C,hC⟩ := hg.bounded_above
  apply SectorExpansion.of_expSmall
    (exponentSum_bddAbove hf.bounded_above hg.bounded_above)
    (exponentSum_finite hf.bounded_above hg.bounded_above hf.finite_above hg.finite_above)
  · filter_upwards [hf.eventually_analytic,hg.eventually_analytic] with z hzf hzg
    exact hzf.mul hzg
  · intro B
    let U := B-(C+1)
    let V := B-(A+1)
    let P : ℂ → ℂ := fun z => ∑ β ∈ (hf.finite_above U).toFinset,Complex.exp ((β:ℂ)*z)*b β z
    let Q : ℂ → ℂ := fun z => ∑ γ ∈ (hg.finite_above V).toFinset,Complex.exp ((γ:ℂ)*z)*c γ z
    have hP : ExpBound (A+1) P := truncation_expBound (fun β hβ => hA hβ) hb U (hf.finite_above U)
    have hr1 : ExpSmall B (fun z => (f z-P z)*g z) := by
      have h := (hf.expSmall_remainder U).mul (hg.expBound (fun γ hγ => hC hγ))
      simpa only [U,sub_add_cancel] using h
    have hr2 : ExpSmall B (fun z => (g z-Q z)*P z) := by
      have h := (hg.expSmall_remainder V).mul hP
      simpa only [V,sub_add_cancel] using h
    have hr : ExpSmall B (fun z => f z*g z-P z*Q z) := by
      convert hr1.add hr2 using 1
      funext z
      ring
    let T := ((hf.finite_above U).toFinset ×ˢ (hg.finite_above V).toFinset).filter
      (fun p => p.1+p.2 < B)
    have hlow : ExpSmall B (fun z => ∑ p ∈ T,
        Complex.exp (((p.1+p.2:ℝ):ℂ)*z)*(b p.1 z*c p.2 z)) := by
      apply ExpSmall.sum
      intro p hp
      have hpr := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      have he := ((hf.finite_above U).mem_toFinset.mp hpr.1).1
      have hF := ((hg.finite_above V).mem_toFinset.mp hpr.2).1
      exact ((hb p.1 he).mul (hc p.2 hF)).expSmall (Finset.mem_filter.mp hp).2
    convert hr.add hlow using 1
    funext z
    have hsplit := rectangle_split hf.bounded_above hg.bounded_above hf.finite_above hg.finite_above
      (B := B) (U := U) (V := V) (fun β hβ => hA hβ) (fun γ hγ => hC hγ)
      (by dsimp [U]; linarith) (by dsimp [V]; linarith) b c z
    change P z*Q z = _ at hsplit
    rw [hsplit]
    dsimp [T]
    ring

lemma SectorSlow.sum {ι : Type*} (S : Finset ι) {f : ι → ℂ → ℂ}
    (h : ∀ i ∈ S, SectorSlow (f i)) : SectorSlow (fun z => ∑ i ∈ S,f i z) := by
  intro ε hε
  exact ExpBound.sum S (fun i hi => h i hi ε hε)

lemma convolution_slow {E F : Set ℝ} (hE : BddAbove E) (hF : BddAbove F)
    (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite) (hFl : ∀ B : ℝ, (F ∩ Ici B).Finite)
    {b c : ℝ → ℂ → ℂ} (hb : ∀ β ∈ E, SectorSlow (b β)) (hc : ∀ γ ∈ F, SectorSlow (c γ))
    (δ : ℝ) : SectorSlow (exponentConvolution hE hF hEl hFl b c δ) := by
  apply SectorSlow.sum
  intro p hp
  have hh := (exponentFiber_finite hE hF hEl hFl δ).mem_toFinset.mp hp
  exact (hb p.1 hh.1).mul (hc p.2 hh.2.1)

lemma convolution_analytic {E F : Set ℝ} (hE : BddAbove E) (hF : BddAbove F)
    (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite) (hFl : ∀ B : ℝ, (F ∩ Ici B).Finite)
    {b c : ℝ → ℂ → ℂ}
    (hb : ∀ β ∈ E, SectorEventually (fun z => AnalyticAt ℂ (b β) z))
    (hc : ∀ γ ∈ F, SectorEventually (fun z => AnalyticAt ℂ (c γ) z)) (δ : ℝ) :
    SectorEventually (fun z => AnalyticAt ℂ (exponentConvolution hE hF hEl hFl b c δ) z) := by
  have hp : ∀ p ∈ (exponentFiber_finite hE hF hEl hFl δ).toFinset,
      SectorEventually (fun z => AnalyticAt ℂ (fun w => b p.1 w*c p.2 w) z) := by
    intro p hp
    have hh := (exponentFiber_finite hE hF hEl hFl δ).mem_toFinset.mp hp
    exact ((hb p.1 hh.1).and (hc p.2 hh.2.1)).mono (fun _ hx => hx.1.mul hx.2)
  exact (SectorEventually.finset_forall _ SectorEventually.truth hp).mono
    (fun _ hz => Finset.analyticAt_fun_sum _ hz)

end DegeneratingTrees.Clock

 

 

 

open Set Complex
namespace DegeneratingTrees.Clock

def wordCoefficient (b : ℝ → ℂ → ℂ) (w : List ℝ) (z : ℂ) : ℂ :=
  (w.map (fun β => b β z)).prod

def wordTerm (b : ℝ → ℂ → ℂ) (w : List ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((w.sum:ℂ)*z)*wordCoefficient b w z

lemma wordTerm_nil (b : ℝ → ℂ → ℂ) (z : ℂ) : wordTerm b [] z=1 := by
  simp [wordTerm,wordCoefficient]

lemma wordTerm_cons (b : ℝ → ℂ → ℂ) (β : ℝ) (w : List ℝ) (z : ℂ) :
    wordTerm b (β::w) z = (Complex.exp ((β:ℂ)*z)*b β z)*wordTerm b w z := by
  simp only [wordTerm,wordCoefficient,List.sum_cons,List.map_cons,List.prod_cons,
    ofReal_add,add_mul,Complex.exp_add]
  ring

lemma power_truncation_words (S : Finset ℝ) (b : ℝ → ℂ → ℂ) (n : ℕ) (z : ℂ) :
    (∑ β ∈ S,Complex.exp ((β:ℂ)*z)*b β z)^n =
      ∑ w ∈ wordsOfLength S n,wordTerm b w z := by
  classical
  induction n with
  | zero => simp [wordsOfLength,wordTerm_nil]
  | succ n ih =>
    rw [pow_succ',ih,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_product (f := fun p : ℝ × List ℝ =>
      (Complex.exp ((p.1:ℂ)*z)*b p.1 z)*wordTerm b p.2 z)]
    apply Finset.sum_bij (fun p _ => p.1::p.2)
    · intro p hp
      have hh := Finset.mem_product.mp hp
      have hw := mem_wordsOfLength.mp hh.2
      exact mem_wordsOfLength.mpr ⟨by simp [hw.1],by simpa using And.intro hh.1 hw.2⟩
    · intro p hp q hq he
      exact Prod.ext (List.cons.inj he).1 (List.cons.inj he).2
    · intro w hw
      have hh := mem_wordsOfLength.mp hw
      cases w with
      | nil => simp at hh
      | cons β w =>
        refine ⟨(β,w),Finset.mem_product.mpr ⟨hh.2 β (by simp),?_⟩,rfl⟩
        exact mem_wordsOfLength.mpr ⟨by simpa using hh.1,
          fun γ hγ => hh.2 γ (List.mem_cons_of_mem _ hγ)⟩
    · intro p hp
      exact (wordTerm_cons b p.1 p.2 z).symm

lemma geometric_truncation_words (S : Finset ℝ) (b : ℝ → ℂ → ℂ) (N : ℕ) (z : ℂ) :
    (∑ n ∈ Finset.range (N+1),(∑ β ∈ S,Complex.exp ((β:ℂ)*z)*b β z)^n) =
      ∑ w ∈ wordsUpTo S N,wordTerm b w z := by
  classical
  simp_rw [power_truncation_words]
  symm
  apply Finset.sum_biUnion
  intro n hn m hm hne
  apply Finset.disjoint_left.mpr
  intro w hwn hwm
  exact hne ((mem_wordsOfLength.mp hwn).1.symm.trans (mem_wordsOfLength.mp hwm).1)

variable {E : Set ℝ} {δ : ℝ} (hδ : 0 < δ) (hE : ∀ β ∈ E, β ≤ -δ)
  (hEl : ∀ B : ℝ, (E ∩ Ici B).Finite)

def geometricCoefficient (b : ℝ → ℂ → ℂ) (β : ℝ) (z : ℂ) : ℂ :=
  ∑ w ∈ (wordFiber_finite hδ hE hEl β).toFinset,wordCoefficient b w z

lemma geometric_coefficient_truncation (b : ℝ → ℂ → ℂ) (B : ℝ) (z : ℂ) :
    (∑ β ∈ (wordSupport_finite hδ hE hEl B).toFinset,
      Complex.exp ((β:ℂ)*z)*geometricCoefficient hδ hE hEl b β z) =
      ∑ w ∈ (wordCut_finite hδ hE hEl B).toFinset,wordTerm b w z := by
  classical
  let S := (wordSupport_finite hδ hE hEl B).toFinset
  let T := (wordCut_finite hδ hE hEl B).toFinset
  have hmaps : ∀ w ∈ T,w.sum ∈ S := by
    intro w hw
    have hh := (wordCut_finite hδ hE hEl B).mem_toFinset.mp hw
    exact (wordSupport_finite hδ hE hEl B).mem_toFinset.mpr ⟨⟨w,hh.1,rfl⟩,hh.2⟩
  calc
    _ = ∑ β ∈ S,∑ w ∈ T with w.sum=β,wordTerm b w z := by
      apply Finset.sum_congr rfl
      intro β hβ
      have hB : B ≤ β := ((wordSupport_finite hδ hE hEl B).mem_toFinset.mp hβ).2
      have he : (wordFiber_finite hδ hE hEl β).toFinset = T.filter (fun w => w.sum=β) := by
        ext w
        simp only [Set.Finite.mem_toFinset,Finset.mem_filter,T,wordFiber,wordCut,mem_ofPred_eq]
        constructor
        · intro hw
          exact ⟨⟨hw.1,by simpa only [hw.2] using hB⟩,hw.2⟩
        · intro hw
          exact ⟨hw.1.1,hw.2⟩
      rw [geometricCoefficient,he,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      simp only [wordTerm,(Finset.mem_filter.mp hw).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hmaps _

lemma words_high {B : ℝ} {N : ℕ} (hN : -δ*((N:ℝ)+1) < B) :
    (wordsUpTo (hEl B).toFinset N).filter (fun w => B ≤ w.sum) =
      (wordCut_finite hδ hE hEl B).toFinset := by
  classical
  ext w
  simp only [Finset.mem_filter,Set.Finite.mem_toFinset]
  constructor
  · intro hw
    exact ⟨fun β hβ => ((hEl B).mem_toFinset.mp ((mem_wordsUpTo.mp hw.1).2 β hβ)).1,hw.2⟩
  · intro hw
    exact ⟨wordCut_subset_words hδ hE (hEl B) hN hw,hw.2⟩

lemma geometric_split (b : ℝ → ℂ → ℂ) {B : ℝ} {N : ℕ}
    (hN : -δ*((N:ℝ)+1) < B) (z : ℂ) :
    (∑ n ∈ Finset.range (N+1),(∑ β ∈ (hEl B).toFinset,Complex.exp ((β:ℂ)*z)*b β z)^n) =
    (∑ β ∈ (wordSupport_finite hδ hE hEl B).toFinset,
      Complex.exp ((β:ℂ)*z)*geometricCoefficient hδ hE hEl b β z) +
      ∑ w ∈ (wordsUpTo (hEl B).toFinset N).filter (fun w => w.sum < B),wordTerm b w z := by
  classical
  rw [geometric_truncation_words,geometric_coefficient_truncation,
    ←words_high hδ hE hEl hN]
  symm
  simpa only [not_le] using Finset.sum_filter_add_sum_filter_not
    (wordsUpTo (hEl B).toFinset N) (fun w => B ≤ w.sum) (fun w => wordTerm b w z)

lemma wordCoefficient_slow {b : ℝ → ℂ → ℂ} (hb : ∀ β ∈ E,SectorSlow (b β))
    {w : List ℝ} (hw : w ∈ exponentWords E) : SectorSlow (wordCoefficient b w) := by
  induction w with
  | nil =>
    intro ε hε
    have h : ExpBound 0 (fun _ : ℂ => (1:ℂ)) := by
      simpa only [ExpBound,zero_mul,Real.exp_zero] using Asymptotics.isBigO_const_one (1:ℂ) sectorInfinity (F := ℝ)
    change ExpBound ε (fun _ => 1)
    exact h.mono hε.le
  | cons β w ih =>
    have hi := ih (fun γ hγ => hw γ (List.mem_cons_of_mem _ hγ))
    change SectorSlow (fun z => b β z*wordCoefficient b w z)
    exact (hb β (hw β (by simp))).mul hi

lemma geometricCoefficient_slow {b : ℝ → ℂ → ℂ} (hb : ∀ β ∈ E,SectorSlow (b β)) (β : ℝ) :
    SectorSlow (geometricCoefficient hδ hE hEl b β) := by
  apply SectorSlow.sum
  intro w hw
  exact wordCoefficient_slow hb ((wordFiber_finite hδ hE hEl β).mem_toFinset.mp hw).1

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
open scoped Asymptotics
namespace DegeneratingTrees.Clock

lemma ExpBound.const (c : ℂ) : ExpBound 0 (fun _ : ℂ => c) := by
  simpa only [ExpBound,zero_mul,Real.exp_zero] using
    Asymptotics.isBigO_const_one c sectorInfinity (F := ℝ)

lemma ExpBound.of_tendsto {f : ℂ → ℂ} {c : ℂ} (hf : Tendsto f sectorInfinity (𝓝 c)) :
    ExpBound 0 f := by
  simpa only [ExpBound,zero_mul,Real.exp_zero] using hf.isBigO_one ℝ

lemma ExpBound.pow {a : ℝ} {f : ℂ → ℂ} (hf : ExpBound a f) (n : ℕ) :
    ExpBound (a*(n:ℝ)) (fun z => f z^n) := by
  induction n with
  | zero => simpa using ExpBound.const 1
  | succ n ih =>
    convert ih.mul hf using 1
    · push_cast; ring
    · funext z; rw [pow_succ]

lemma ExpBound.congr {a : ℝ} {f g : ℂ → ℂ} (hf : ExpBound a f)
    (he : f =ᶠ[sectorInfinity] g) : ExpBound a g := hf.congr' he (EventuallyEq.refl _ _)

lemma ExpSmall.congr {B : ℝ} {f g : ℂ → ℂ} (hf : ExpSmall B f)
    (he : f =ᶠ[sectorInfinity] g) : ExpSmall B g := by
  obtain ⟨a,ha,hf⟩ := hf
  exact ⟨a,ha,hf.congr he⟩

lemma ExpBound.tendsto_zero {a : ℝ} {f : ℂ → ℂ} (hf : ExpBound a f) (ha : a < 0) :
    Tendsto f sectorInfinity (𝓝 0) := by
  apply Asymptotics.IsBigO.trans_tendsto hf
  apply Real.tendsto_exp_atBot.comp
  exact tendsto_re_sectorInfinity.const_mul_atTop_of_neg ha

lemma inverse_one_sub_tendsto {f : ℂ → ℂ} (hf : Tendsto f sectorInfinity (𝓝 0)) :
    Tendsto (fun z => (1-f z)⁻¹) sectorInfinity (𝓝 1) := by
  simpa using (tendsto_const_nhds.sub hf).inv₀ (by norm_num : (1:ℂ)-0≠0)

lemma inverse_one_sub_bound {f : ℂ → ℂ} (hf : Tendsto f sectorInfinity (𝓝 0)) :
    ExpBound 0 (fun z => (1-f z)⁻¹) := ExpBound.of_tendsto (inverse_one_sub_tendsto hf)

lemma one_sub_eventually_ne {f : ℂ → ℂ} (hf : Tendsto f sectorInfinity (𝓝 0)) :
    ∀ᶠ z in sectorInfinity, 1-f z≠0 := by
  have ht : Tendsto (fun z => (1:ℂ)-f z) sectorInfinity (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hf
  exact ht.eventually (eventually_ne_nhds (by norm_num : (1:ℂ)≠0))

lemma inverse_difference_small {B : ℝ} {f g : ℂ → ℂ}
    (hf : Tendsto f sectorInfinity (𝓝 0)) (hg : Tendsto g sectorInfinity (𝓝 0))
    (he : ExpSmall B (fun z => f z-g z)) :
    ExpSmall B (fun z => (1-f z)⁻¹-(1-g z)⁻¹) := by
  have h := (he.mul (inverse_one_sub_bound hf)).mul (inverse_one_sub_bound hg)
  simp only [add_zero] at h
  apply h.congr
  filter_upwards [one_sub_eventually_ne hf,one_sub_eventually_ne hg] with z hzf hzg
  field_simp
  ring

lemma geom_inverse_error {f : ℂ → ℂ} {a B : ℝ} {N : ℕ}
    (hf : ExpBound a f) (ha : a < 0) (hN : a*((N:ℝ)+1) < B) :
    ExpSmall B (fun z => (1-f z)⁻¹-∑ n ∈ Finset.range (N+1),f z^n) := by
  have ht := hf.tendsto_zero ha
  have hpow := (hf.pow (N+1)).mul (inverse_one_sub_bound ht)
  simp only [add_zero,Nat.cast_add,Nat.cast_one] at hpow
  apply (show ExpSmall B (fun z => f z^(N+1)*(1-f z)⁻¹) from ⟨_,hN,hpow⟩).congr
  filter_upwards [one_sub_eventually_ne ht] with z hz
  have he := geom_sum_mul_neg (f z) (N+1)
  apply (mul_right_cancel₀ hz)
  rw [sub_mul,inv_mul_cancel₀ hz,mul_assoc,inv_mul_cancel₀ hz,mul_one,he]
  ring

lemma SectorExpansion.negative_bound {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) {δ : ℝ} (hδ : 0 < δ) (hE : ∀ β ∈ E,β ≤ -δ) :
    ExpBound (-δ/2) f := by
  have hem : (hf.finite_above (-δ/2)).toFinset=∅ := by
    classical
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro β hβ
    have hh := (hf.finite_above (-δ/2)).mem_toFinset.mp hβ
    have hu := hE β hh.1
    have hl : -δ/2 ≤ β := hh.2
    linarith
  obtain ⟨a,ha,he⟩ := hf.expSmall_remainder (-δ/2)
  simp only [hem,Finset.sum_empty,sub_zero] at he
  exact he.mono ha.le

lemma truncation_negative_bound {E : Set ℝ} {b : ℝ → ℂ → ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hE : ∀ β ∈ E,β ≤ -δ) (hb : ∀ β ∈ E,SectorSlow (b β))
    (B : ℝ) (hEl : (E ∩ Ici B).Finite) :
    ExpBound (-δ/2) (fun z => ∑ β ∈ hEl.toFinset,Complex.exp ((β:ℂ)*z)*b β z) := by
  apply ExpBound.sum
  intro β hβ
  have he := (hEl.mem_toFinset.mp hβ).1
  exact ((hb β he (δ/2) (by positivity)).expTerm β).mono (by linarith [hE β he])

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex
namespace DegeneratingTrees.Clock

theorem SectorExpansion.geometric_inverse {f : ℂ → ℂ} {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hf : SectorExpansion f E b) {δ : ℝ} (hδ : 0 < δ)
    (hE : ∀ β ∈ E,β ≤ -δ) (hb : ∀ β ∈ E,SectorSlow (b β)) :
    SectorExpansion (fun z => (1-f z)⁻¹) (wordSupport E)
      (geometricCoefficient hδ hE hf.finite_above b) := by
  classical
  have hneg := hf.negative_bound hδ hE
  have ht := hneg.tendsto_zero (by linarith : -δ/2<0)
  apply SectorExpansion.of_expSmall (wordSupport_bddAbove hδ.le hE)
    (wordSupport_finite hδ hE hf.finite_above)
  · filter_upwards [hf.eventually_analytic,one_sub_eventually_ne ht] with z hzf hzne
    exact (analyticAt_const.sub hzf).inv hzne
  · intro B
    let S := (hf.finite_above B).toFinset
    let P : ℂ → ℂ := fun z => ∑ β ∈ S,Complex.exp ((β:ℂ)*z)*b β z
    have hP : ExpBound (-δ/2) P := truncation_negative_bound hδ hE hb B (hf.finite_above B)
    have hPt : Tendsto P sectorInfinity (𝓝 0) := hP.tendsto_zero (by linarith)
    have hinv : ExpSmall B (fun z => (1-f z)⁻¹-(1-P z)⁻¹) :=
      inverse_difference_small ht hPt (hf.expSmall_remainder B)
    obtain ⟨N,hN⟩ := exists_nat_gt (-2*B/δ)
    have hN' : -δ/2*((N:ℝ)+1) < B := by
      have hh := (div_lt_iff₀ hδ).mp hN
      nlinarith
    have hN'' : -δ*((N:ℝ)+1) < B := by
      have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
      nlinarith
    have hgeom := geom_inverse_error hP (by linarith : -δ/2<0) hN'
    let T := (wordsUpTo S N).filter (fun w => w.sum < B)
    have hlow : ExpSmall B (fun z => ∑ w ∈ T,wordTerm b w z) := by
      apply ExpSmall.sum
      intro w hw
      have hm := (mem_wordsUpTo.mp (Finset.mem_filter.mp hw).1).2
      have hwE : w ∈ exponentWords E := fun β hβ =>
        ((hf.finite_above B).mem_toFinset.mp (hm β hβ)).1
      exact (wordCoefficient_slow hb hwE).expSmall (Finset.mem_filter.mp hw).2
    convert (hinv.add hgeom).add hlow using 1
    funext z
    have he := geometric_split hδ hE hf.finite_above b hN'' z
    change (∑ n ∈ Finset.range (N+1),P z^n) = _ at he
    rw [he]
    dsimp [T,S]
    ring

lemma wordCoefficient_analytic {E : Set ℝ} {b : ℝ → ℂ → ℂ}
    (hb : ∀ β ∈ E,SectorEventually (fun z => AnalyticAt ℂ (b β) z))
    {w : List ℝ} (hw : w ∈ exponentWords E) :
    SectorEventually (fun z => AnalyticAt ℂ (wordCoefficient b w) z) := by
  induction w with
  | nil =>
    exact SectorEventually.truth.mono (fun z _ => by
      change AnalyticAt ℂ (fun _ => (1:ℂ)) z
      exact analyticAt_const)
  | cons β w ih =>
    have hi := ih (fun γ hγ => hw γ (List.mem_cons_of_mem _ hγ))
    exact ((hb β (hw β (by simp))).and hi).mono (fun z hz => by
      change AnalyticAt ℂ (fun z => b β z*wordCoefficient b w z) z
      exact hz.1.mul hz.2)

lemma geometricCoefficient_analytic {E : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hE : ∀ β ∈ E, β ≤ -δ) (hEl : ∀ B : ℝ,(E ∩ Ici B).Finite)
    {b : ℝ → ℂ → ℂ}
    (hb : ∀ β ∈ E,SectorEventually (fun z => AnalyticAt ℂ (b β) z)) (β : ℝ) :
    SectorEventually (fun z => AnalyticAt ℂ (geometricCoefficient hδ hE hEl b β) z) := by
  have hw : ∀ w ∈ (wordFiber_finite hδ hE hEl β).toFinset,
      SectorEventually (fun z => AnalyticAt ℂ (wordCoefficient b w) z) := by
    intro w hw
    exact wordCoefficient_analytic hb ((wordFiber_finite hδ hE hEl β).mem_toFinset.mp hw).1
  exact (SectorEventually.finset_forall _ SectorEventually.truth hw).mono
    (fun z hz => Finset.analyticAt_fun_sum _ hz)

end DegeneratingTrees.Clock
end

end OAI
