import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Entropy.FineCharts

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma fineCoordinate_continuous (k χ ε δ : ℝ) (w : ℂ) (n : ℕ) :
    Continuous (fineCoordinate k χ ε δ w · n) := by
  exact (fineInverse k χ ε δ _).continuous.comp
    ((((contDiff_standardLift k).continuous).iterate n).sub continuous_const)
lemma fineTrapped_closed (k χ ε δ : ℝ) (w : ℂ) (n : ℕ) :
    IsClosed (fineTrapped k χ ε δ w n) := by
  have he : fineTrapped k χ ε δ w n=⋂ j : ℕ, ⋂ _ : j≤n, {v | ‖fineCoordinate k χ ε δ w
    (w+fineFrame k χ ε δ (complexProjection w) v) j‖≤1} := by
    ext v; simp only [fineTrapped,mem_ofPred_eq,mem_iInter]
  rw [he]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_le (((fineCoordinate_continuous k χ ε δ w j).comp
    (continuous_const.add (fineFrame k χ ε δ _).continuous)).norm) continuous_const

def fineLiftTrapped (k χ ε δ : ℝ) (w : ℂ) (n : ℕ) : Set ℂ :=
  {p | ∀ j : ℕ, j≤n → ‖fineCoordinate k χ ε δ w p j‖≤1}
lemma fineLiftTrapped_image (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (w : ℂ)
    (hw : FineRegular k χ ε (complexProjection w)) (n : ℕ) :
    fineLiftTrapped k χ ε δ w n=
      (fun v => w+fineFrame k χ ε δ (complexProjection w) v) '' fineTrapped k χ ε δ w n := by
  ext p
  constructor
  · intro hp
    let v := fineInverse k χ ε δ (complexProjection w) (p-w)
    have he : w+fineFrame k χ ε δ (complexProjection w) v=p := by
      dsimp [v]
      rw [fineFrame_inverse k χ ε hδ _ hw.1]
      abel
    exact ⟨v,by change ∀ j, j≤n → _; rw [he]; exact hp,he⟩
  · rintro ⟨v,hv,rfl⟩
    exact hv

lemma volume_pairToComplex_image {S : Set RealPlane} (hS : MeasurableSet S) :
    volume (pairToComplex '' S)=volume S := by
  have he : pairToComplex '' S=Complex.measurableEquivRealProd ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨v,hv,rfl⟩; exact hv
    · intro hz
      exact ⟨complexToPair z,hz,pairToComplex_complexToPair z⟩
  rw [he]
  exact Complex.volume_preserving_equiv_real_prod.measure_preimage hS.nullMeasurableSet

noncomputable def fineVolumeFactor (k χ ε δ : ℝ) (z : Torus) : ℝ :=
  |(fineSize k χ ε δ z • lyapunovFrame k χ z).det|
lemma fineLiftTrapped_volume_eq (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) (w : ℂ)
    (hw : FineRegular k χ ε (complexProjection w)) (n : ℕ) :
    volume (fineLiftTrapped k χ ε δ w n)=
      ENNReal.ofReal (fineVolumeFactor k χ ε δ (complexProjection w))*volume (fineTrapped k χ ε δ w n) := by
  rw [fineLiftTrapped_image k χ ε hδ w hw n]
  have he : (fun v => w+fineFrame k χ ε δ (complexProjection w) v) '' fineTrapped k χ ε δ w n=
      (fun z : ℂ => w+z) '' ((fineSize k χ ε δ (complexProjection w) • lyapunovFrame k χ (complexProjection w)) ''
        (pairToComplex '' fineTrapped k χ ε δ w n)) := by
    rw [Set.image_image,Set.image_image]
    rfl
  rw [he,Set.image_add_left,measure_preimage_add,Measure.addHaar_image_continuousLinearMap,
    volume_pairToComplex_image (fineTrapped_closed k χ ε δ w n).measurableSet]
  rfl

theorem fineLiftTrapped_volume (k χ ε δ : ℝ) (hδ : 0<δ)
    (hq : Real.exp (-χ+ε)+δ<1) (w : ℂ)
    (hw : ∀ n : ℕ, FineRegular k χ ε (complexProjection ((standardLift k)^[n] w))) (n : ℕ) :
    volume (fineLiftTrapped k χ ε δ w n)≤
      ENNReal.ofReal (4*fineVolumeFactor k χ ε δ (complexProjection w)*(Real.exp (-χ+ε)+δ)^n) := by
  rw [fineLiftTrapped_volume_eq k χ ε hδ w (hw 0) n]
  calc
    _ ≤ ENNReal.ofReal (fineVolumeFactor k χ ε δ (complexProjection w))*
        ENNReal.ofReal (4*(Real.exp (-χ+ε)+δ)^n) :=
      mul_le_mul le_rfl (fineTrapped_volume k χ ε δ hδ hq w hw n) zero_le zero_le
    _ = _ := by rw [←ENNReal.ofReal_mul (show 0≤fineVolumeFactor k χ ε δ (complexProjection w) from abs_nonneg _)]; congr 1; ring

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

def complexCell : Set ℂ := {z | z.re∈Ico (0 : ℝ) 1 ∧ z.im∈Ico (0 : ℝ) 1}
lemma complexRep_projection_of_cell {z : ℂ} (hz : z∈complexCell) : complexRep (complexProjection z)=z := by
  apply Complex.ext
  · exact circleRep_coe_of_mem hz.1
  · exact circleRep_coe_of_mem hz.2
lemma measurePreserving_complexProjection_cell :
    MeasurePreserving complexProjection (volume.restrict complexCell) area := by
  have hp := (AddCircle.measurePreserving_mk (1 : ℝ) 0).prod (AddCircle.measurePreserving_mk (1 : ℝ) 0)
  simp only [zero_add] at hp
  rw [←restrict_Ico_eq_restrict_Ioc,Measure.prod_restrict] at hp
  have hc := Complex.volume_preserving_equiv_real_prod.restrict_preimage (measurableSet_Ico.prod measurableSet_Ico :
    MeasurableSet (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1))
  exact hp.comp hc
lemma area_le_volume_of_complexRep_subset {S : Set Torus} (hS : MeasurableSet S) {V : Set ℂ}
    (hsub : ∀ z∈S,complexRep z∈V) : area S≤volume V := by
  rw [←measurePreserving_complexProjection_cell.measure_preimage hS.nullMeasurableSet,
    Measure.restrict_apply (measurePreserving_complexProjection_cell.measurable hS)]
  apply measure_mono
  intro z hz
  have hh := hsub (complexProjection z) hz.1
  rwa [complexRep_projection_of_cell hz.2] at hh
lemma measurableSet_fineLiftTrapped (k χ ε δ : ℝ) (w : ℂ) (n : ℕ) :
    MeasurableSet (fineLiftTrapped k χ ε δ w n) := by
  have he : fineLiftTrapped k χ ε δ w n=⋂ j : ℕ,⋂ _ : j≤n,{p | ‖fineCoordinate k χ ε δ w p j‖≤1} := by
    ext p; simp only [fineLiftTrapped,mem_ofPred_eq,mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
    (isClosed_le (fineCoordinate_continuous k χ ε δ w j).norm continuous_const).measurableSet))

lemma exists_fineVolumeFactor_bound (k χ ε : ℝ) {δ : ℝ} (hδ : 0<δ) :
    ∃ C : ℝ,0<C ∧ ∀ z : Torus,fineVolumeFactor k χ ε δ z≤C := by
  let η := fineScale k ε δ
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : ℂ →L[ℝ] ℂ) η).exists_bound_of_continuousOn
    (ContinuousLinearMap.continuous_det (𝕜:=ℝ) (E:=ℂ)).continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z
  apply (hC (fineSize k χ ε δ z • lyapunovFrame k χ z) ?_).trans (le_max_right _ _)
  rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (fineSize_pos k χ ε hδ z)]
  exact (mul_le_mul_of_nonneg_left (lyapunovFrame_norm_le k χ z) (fineSize_pos k χ ε hδ z).le).trans
    (by simpa only [mul_one] using fineSize_le_scale k χ ε hδ z)

lemma circle_coe_eq_of_close {x y : ℝ} (hxy : (x : Circle)=(y : Circle)) (hd : |x-y|<1) : x=y := by
  have hz : ((x-y : ℝ) : Circle)=0 := by rw [QuotientAddGroup.mk_sub,hxy,sub_self]
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  have hn' : (n : ℝ)=x-y := by simpa only [zsmul_eq_mul,mul_one] using hn
  have hab : (-1 : ℝ)<(n : ℝ) ∧ (n : ℝ)<1 := by rw [hn']; exact abs_lt.mp hd
  have hn0 : n=0 := by
    have h1 : (-1 : ℤ)<n := by exact_mod_cast hab.1
    have h2 : n<(1 : ℤ) := by exact_mod_cast hab.2
    omega
  subst n
  simp only [Int.cast_zero] at hn'
  linarith
lemma complexProjection_eq_of_close {z w : ℂ} (hz : complexProjection z=complexProjection w) (hd : ‖z-w‖<1) : z=w := by
  apply Complex.ext
  · exact circle_coe_eq_of_close (congrArg Prod.fst hz) ((Complex.abs_re_le_norm (z-w)).trans_lt hd)
  · exact circle_coe_eq_of_close (congrArg Prod.snd hz) ((Complex.abs_im_le_norm (z-w)).trans_lt hd)

end StandardMapEntropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]

def history (X : ℕ → Ω → α) (n : ℕ) : Ω → (Fin n → α) := fun x i => X i.val x
omit [Fintype α] [MeasurableSingletonClass α] in
lemma history_measurable (X : ℕ → Ω → α) (hX : ∀ i,Measurable (X i)) (n : ℕ) :
    Measurable (history X n) := Measurable.of_eval (fun i => hX i.val)
noncomputable def historySnocEquiv (n : ℕ) : (Fin (n+1) → α) ≃ (Fin n → α)×α where
  toFun v := (fun i => v i.castSucc,v (Fin.last n))
  invFun v := Fin.lastCases v.2 v.1
  left_inv v := by funext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv v := by ext i <;> simp
omit [MeasurableSpace Ω] [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma historySnocEquiv_apply (X : ℕ → Ω → α) (n : ℕ) (x : Ω) :
    historySnocEquiv n (history X (n+1) x)=(history X n x,X n x) := rfl
omit [IsProbabilityMeasure μ] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma cond_history_succ (X : ℕ → Ω → α) (n : ℕ) (Y : Ω → β) :
    cond μ (history X (n+1)) Y=cond μ (history X n) Y+cond μ (X n) (fun x => (history X n x,Y x)) := by
  have he := cond_equiv_left μ (history X (n+1)) Y (historySnocEquiv n)
  simp only [Function.comp_def,historySnocEquiv_apply] at he
  rw [←he,cond_chain]
omit [IsProbabilityMeasure μ] [MeasurableSpace β] [MeasurableSingletonClass β] in
lemma cond_history_one (X : ℕ → Ω → α) (Y : Ω → β) : cond μ (history X 1) Y=cond μ (X 0) Y := by
  have he := cond_equiv_left μ (history X 1) Y (Equiv.funUnique (Fin 1) α)
  simpa only [Function.comp_def,Equiv.funUnique_apply,history,Fin.default_eq_zero,Fin.val_zero] using he.symm

lemma cond_history_markov (X : ℕ → Ω → α) (hX : ∀ i,Measurable (X i))
    (Y : Ω → β) (hY : Measurable Y) (R : ℕ → β → γ) (n : ℕ) :
    cond μ (history X (n+1)) Y≤obs μ (X 0)+
      ∑ i∈Finset.range n,cond μ (X (i+1)) (fun x => (R (i+1) (Y x),X i x)) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero]
    change cond μ (history X 1) Y≤obs μ (X 0)
    rw [cond_history_one]
    exact cond_le_obs μ (X 0) Y (hX 0) hY
  | succ n ih =>
    rw [cond_history_succ,Finset.sum_range_succ,←add_assoc]
    apply add_le_add ih
    have he : (fun x => (R (n+1) (Y x),X n x))=
        (fun v : (Fin (n+1)→α)×β => (R (n+1) v.2,v.1 ⟨n,by omega⟩)) ∘
          (fun x => (history X (n+1) x,Y x)) := rfl
    rw [he]
    exact cond_factor_right μ _ _ _ (hX (n+1)) ((history_measurable X hX _).prodMk hY)

lemma obs_history_markov (X : ℕ → Ω → α) (hX : ∀ i,Measurable (X i))
    (Y : Ω → β) (hY : Measurable Y) (R : ℕ → β → γ) (n : ℕ) :
    obs μ (history X (n+1))≤obs μ Y+obs μ (X 0)+
      ∑ i∈Finset.range n,cond μ (X (i+1)) (fun x => (R (i+1) (Y x),X i x)) := by
  have hc := cond_history_markov μ X hX Y hY R n
  have hh := obs_pair_ge_left μ (history X (n+1)) Y (history_measurable X hX _) hY
  change obs μ (fun x => (history X (n+1) x,Y x))-obs μ Y≤_ at hc
  linarith

lemma cond_support_integral (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (S : β → Finset α) (hS : ∀ x,p x∈S (q x)) (g : β → ℝ)
    (hg : ∀ b,Real.log ((S b).card : ℝ)≤g b) : cond μ p q≤∫ x,g (q x) ∂μ := by
  have hh := cond_support_bound μ p q hp hq S hS
  have hs : (∑ b,mass μ q b*Real.log ((S b).card : ℝ))≤∑ b,mass μ q b*g b :=
    Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hg b) (mass_nonneg μ q b))
  exact (hh.trans hs).trans_eq (sum_mass_mul_integral μ q hq g)

lemma log_card_le_of_card_le {A : Type*} (s : Finset A) {D : ℕ} (hD : 0<D) (hc : s.card≤D) :
    Real.log (s.card : ℝ)≤Real.log (D : ℝ) := by
  by_cases hs : s.card=0
  · rw [hs,Nat.cast_zero,Real.log_zero]
    exact Real.log_nonneg (by exact_mod_cast hD)
  · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)) (by exact_mod_cast hc)

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {α β : Type*} [Fintype α] [Fintype β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

lemma cond_support_bound_ae (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (S : β → Finset α) (hS : ∀ᵐ x ∂μ,p x∈S (q x)) :
    cond μ p q≤∑ b,mass μ q b*Real.log ((S b).card : ℝ) := by
  classical
  have rz (b : β) (a : α) (ha : a∉S b) : mass μ (fun x => (p x,q x)) (a,b)=0 := by
    have hs : (fun x => (p x,q x)) ⁻¹' {(a,b)}⊆{x | ¬p x∈S (q x)} := by
      intro x hx hh
      obtain ⟨hx1,hx2⟩ := Prod.mk.inj hx
      exact ha (hx1 ▸ hx2 ▸ hh)
    have hm := measure_mono_null hs (ae_iff.mp hS)
    simp only [mass,hm,ENNReal.toReal_zero]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun b _ =>
    shannon_support_bound (fun a => mass μ (fun x => (p x,q x)) (a,b))
      (fun a => mass_nonneg μ _ _) (S b) (rz b))
  simp only [←mass_joint_col μ p q hp hq,shannon,Finset.sum_add_distrib] at hh
  unfold cond obs shannon
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  linarith
lemma cond_support_integral_ae (p : Ω → α) (q : Ω → β) (hp : Measurable p) (hq : Measurable q)
    (S : β → Finset α) (hS : ∀ᵐ x ∂μ,p x∈S (q x)) (g : β → ℝ)
    (hg : ∀ b,Real.log ((S b).card : ℝ)≤g b) : cond μ p q≤∫ x,g (q x) ∂μ := by
  have hh := cond_support_bound_ae μ p q hp hq S hS
  have hs : (∑ b,mass μ q b*Real.log ((S b).card : ℝ))≤∑ b,mass μ q b*g b :=
    Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hg b) (mass_nonneg μ q b))
  exact (hh.trans hs).trans_eq (sum_mass_mul_integral μ q hq g)

lemma mass_le_one (p : Ω → α) (hp : Measurable p) (a : α) : mass μ p a≤1 := by
  have hs := Finset.single_le_sum (fun b _ => mass_nonneg μ p b) (Finset.mem_univ a)
  simpa only [mass_sum μ p hp,measure_univ,ENNReal.toReal_one] using hs

lemma obs_lower_small_atoms (p : Ω → α) (hp : Measurable p) (a₀ : α) (I : ℝ)
    (hsmall : ∀ a : α,a≠a₀ → mass μ p a≤Real.exp (-I)) :
    (1-mass μ p a₀)*I≤obs μ p := by
  classical
  have hterm (a : α) : (if a=a₀ then 0 else mass μ p a*I)≤Real.negMulLog (mass μ p a) := by
    by_cases ha : a=a₀
    · rw [ite_eq_left ha]
      exact Real.negMulLog_nonneg (mass_nonneg μ p a) (mass_le_one μ p hp a)
    · rw [ite_eq_right ha]
      by_cases hz : mass μ p a=0
      · rw [hz,zero_mul,Real.negMulLog_zero]
      · have hpos : 0 < mass μ p a := lt_of_le_of_ne (mass_nonneg μ p a) (Ne.symm hz)
        have hh := Real.log_le_log hpos (hsmall a ha)
        rw [Real.log_exp] at hh
        unfold Real.negMulLog
        nlinarith [mass_nonneg μ p a]
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => hterm a)
  have he : (∑ a : α,if a=a₀ then 0 else mass μ p a*I)=(1-mass μ p a₀)*I := by
    have ht : (∑ a : α,if a=a₀ then 0 else mass μ p a*I)+mass μ p a₀*I=∑ a : α,mass μ p a*I := by
      have hsingle : (∑ a : α,if a=a₀ then mass μ p a*I else 0)=mass μ p a₀*I := by simp
      rw [←hsingle]
      rw [←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun a _ => by split_ifs <;> simp)
    rw [←Finset.sum_mul,mass_sum μ p hp,measure_univ,ENNReal.toReal_one,one_mul] at ht
    linarith
  simpa only [he,obs,shannon] using hs

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.LocalCoding
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {ι : Type*} [DecidableEq ι]

noncomputable def truncate (A : Finset ι) (a : ι) : Option A :=
  if h : a∈A then some ⟨a,h⟩ else none
@[simp] lemma truncate_none_iff (A : Finset ι) (a : ι) : truncate A a=none ↔ a∉A := by
  simp only [truncate]
  split_ifs <;> simp_all
lemma truncate_some (A : Finset ι) (a : ι) (ha : a∈A) : truncate A a=some ⟨a,ha⟩ := by simp [truncate,ha]
lemma truncate_eq_some_iff (A : Finset ι) (a : ι) (b : A) : truncate A a=some b ↔ a=b.val := by
  by_cases ha : a∈A
  · simp only [truncate_some A a ha,Option.some.injEq]
    exact Subtype.ext_iff
  · have hab : a ≠ b.val := fun hh => ha (hh ▸ b.property)
    simp [truncate, ha, hab]
lemma truncate_inj (A : Finset ι) {a b : ι} (ha : a∈A) (hb : b∈A)
    (h : truncate A a=truncate A b) : a=b := by
  rw [truncate_some A a ha,truncate_some A b hb] at h
  exact congrArg Subtype.val (Option.some.inj h)

def reach (S : ι → Finset ι) (A : Finset ι) : ℕ → Finset ι
  | 0 => A
  | n+1 => reach S A n ∪ (reach S A n).biUnion S
lemma reach_step (S : ι → Finset ι) (A : Finset ι) (n : ℕ) : reach S A n⊆reach S A (n+1) := Finset.subset_union_left
lemma reach_mono (S : ι → Finset ι) (A : Finset ι) : Monotone (reach S A) :=
  monotone_nat_of_le_succ (reach_step S A)
lemma base_subset_reach (S : ι → Finset ι) (A : Finset ι) (n : ℕ) : A⊆reach S A n := reach_mono S A (Nat.zero_le n)
lemma next_mem_reach (S : ι → Finset ι) (A : Finset ι) {n : ℕ} {a b : ι}
    (ha : a∈reach S A n) (hb : b∈S a) : b∈reach S A (n+1) :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a,ha,hb⟩)
lemma path_mem_reach (S : ι → Finset ι) (A : Finset ι) (x : ℕ → ι)
    (h0 : x 0∈A) (hstep : ∀ i,x (i+1)∈S (x i)) (n : ℕ) : x n∈reach S A n := by
  induction n with
  | zero => exact h0
  | succ n ih => exact next_mem_reach S A ih (hstep n)

instance optionFinsetMeasurableSpace (A : Finset ι) : MeasurableSpace (Option A) := ⊤
instance optionFinsetMeasurableSingleton (A : Finset ι) : MeasurableSingletonClass (Option A) :=
  ⟨fun _ => trivial⟩

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
lemma measurable_truncate (A : Finset ι) : Measurable (truncate A) := measurable_of_countable _
noncomputable def maskedState (A R : Finset ι) (f : Ω → Ω) (p : Ω → ι) (i : ℕ) (x : Ω) : Option R :=
  if p x∈A then truncate R (p (f^[i] x)) else none
lemma measurable_maskedState (A R : Finset ι) (f : Ω → Ω) (p : Ω → ι)
    (hf : Measurable f) (hp : Measurable p) (i : ℕ) : Measurable (maskedState A R f p i) := by
  exact Measurable.ite (hp (A.measurableSet)) ((measurable_truncate R).comp (hp.comp (hf.iterate i))) measurable_const
omit [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma maskedState_of_mem (A R : Finset ι) (f : Ω → Ω) (p : Ω → ι) (i : ℕ) {x : Ω} (hx : p x∈A) :
    maskedState A R f p i x=truncate R (p (f^[i] x)) := by simp only [maskedState,hx,↓reduceIte]
omit [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma maskedState_of_not_mem (A R : Finset ι) (f : Ω → Ω) (p : Ω → ι) (i : ℕ) {x : Ω} (hx : p x∉A) :
    maskedState A R f p i x=none := by simp only [maskedState,hx,↓reduceIte]
omit [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma maskedState_zero_none (A R : Finset ι) (hAR : A⊆R) (f : Ω → Ω) (p : Ω → ι) (x : Ω) :
    maskedState A R f p 0 x=none ↔ p x∉A := by
  by_cases hx : p x∈A
  · rw [maskedState_of_mem A R f p 0 hx]
    simp only [Function.iterate_zero,Function.id_def,truncate_none_iff]
    exact iff_of_false (fun h => h (hAR hx)) (fun h => h hx)
  · rw [maskedState_of_not_mem A R f p 0 hx]
    exact iff_of_true rfl hx

omit [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma ae_transition_orbit (μ : Measure Ω) (f : Ω → Ω) (hf : MeasurePreserving f μ μ)
    (p : Ω → ι) (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x)) :
    ∀ᵐ x ∂μ,∀ i : ℕ,p (f^[i+1] x)∈S (p (f^[i] x)) := by
  rw [ae_all_iff]
  intro i
  have hh := (hf.iterate i).quasiMeasurePreserving.ae hS
  simpa only [Function.iterate_succ_apply'] using hh

end StandardMapEntropy.LocalCoding

end
section
namespace StandardMapEntropy.LocalCoding
open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators
variable {ι : Type*} [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

noncomputable def transitionSupport (S : ι → Finset ι) (R K : Finset ι) :
    Option K×Option R → Finset (Option R)
  | (_,none) => {none}
  | (none,some a) => (S a.val).image (truncate R)
  | (some b,some _) => {truncate R b.val}
omit [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma transitionSupport_log_bound (S : ι → Finset ι) (R K : Finset ι) {D : ℕ}
    (hD : 0<D) (hcard : ∀ a,(S a).card≤D) (b : Option K×Option R) :
    Real.log ((transitionSupport S R K b).card : ℝ)≤ if b.1=none then Real.log (D : ℝ) else 0 := by
  rcases b with ⟨b,c⟩
  cases c with
  | none =>
    simp only [transitionSupport,Finset.card_singleton,Nat.cast_one,Real.log_one]
    split_ifs
    · exact Real.log_nonneg (by exact_mod_cast hD)
    · exact le_rfl
  | some c =>
    cases b with
    | none =>
      simp only [transitionSupport,↓reduceIte]
      exact Entropy.log_card_le_of_card_le _ hD (Finset.card_image_le.trans (hcard c.val))
    | some b => simp only [transitionSupport,Finset.card_singleton,Nat.cast_one,Real.log_one,Option.some_ne_none,↓reduceIte,le_refl]

omit [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] in
lemma masked_transition_mem (f : Ω → Ω) (p : Ω → ι) (S : ι → Finset ι) (A K : Finset ι)
    (N i : ℕ) (hi : i≤N) (x : Ω)
    (hx : ∀ j : ℕ,p (f^[j+1] x)∈S (p (f^[j] x))) :
    maskedState A (reach S A N) f p (i+1) x∈transitionSupport S (reach S A N) K
      (truncate K (p (f^[i+1] x)),maskedState A (reach S A N) f p i x) := by
  by_cases hA : p x∈A
  · have hreach := path_mem_reach S A (fun j => p (f^[j] x)) hA hx i
    have hr : p (f^[i] x)∈reach S A N := reach_mono S A hi hreach
    rw [maskedState_of_mem A _ f p i hA,truncate_some _ _ hr,maskedState_of_mem A _ f p (i+1) hA]
    by_cases hK : p (f^[i+1] x)∈K
    · rw [truncate_some K _ hK]
      exact Finset.mem_singleton_self _
    · rw [(truncate_none_iff K _).mpr hK]
      exact Finset.mem_image.mpr ⟨p (f^[i+1] x),hx i,rfl⟩
  · rw [maskedState_of_not_mem A _ f p i hA,maskedState_of_not_mem A _ f p (i+1) hA]
    exact Finset.mem_singleton_self _

omit [Countable ι] [IsProbabilityMeasure μ] in
lemma tail_integral (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → ι)
    (hp : Measurable p) (K : Finset ι) (i : ℕ) (c : ℝ) :
    (∫ x,if truncate K (p (f^[i] x))=none then c else 0 ∂μ)=
      (μ {x | p x∉K}).toReal*c := by
  have hset : MeasurableSet {x | p x∉K} := (hp K.measurableSet).compl
  have he : (fun x => if truncate K (p (f^[i] x))=none then c else 0)=
      ((f^[i]) ⁻¹' {x | p x∉K}).indicator (fun _ => c) := by
    funext x
    by_cases hx : p (f^[i] x) ∈ K <;> simp [Set.indicator, hx]
  rw [he,integral_indicator ((hf.measurable.iterate i) hset),integral_const,Measure.real,Measure.restrict_apply_univ,
    (hf.iterate i).measure_preimage hset.nullMeasurableSet]
  rfl

lemma masked_cond_le_tail (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → ι) (hp : Measurable p)
    (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x)) {D : ℕ} (hD : 0<D)
    (hcard : ∀ a,(S a).card≤D) (A K : Finset ι) (N i : ℕ) (hi : i≤N) :
    Entropy.cond μ (maskedState A (reach S A N) f p (i+1))
      (fun x => (truncate K (p (f^[i+1] x)),maskedState A (reach S A N) f p i x))≤
      (μ {x | p x∉K}).toReal*Real.log (D : ℝ) := by
  have hm (j : ℕ) := measurable_maskedState A (reach S A N) f p hf.measurable hp j
  have ht := Entropy.cond_support_integral_ae μ _ _ (hm (i+1))
    (((measurable_truncate K).comp (hp.comp (hf.measurable.iterate (i+1)))).prodMk (hm i))
    (transitionSupport S (reach S A N) K)
    (by filter_upwards [ae_transition_orbit μ f hf p S hS] with x hx; exact masked_transition_mem f p S A K N i hi x hx)
    (fun b => if b.1=none then Real.log (D : ℝ) else 0)
    (transitionSupport_log_bound S (reach S A N) K hD hcard)
  simpa only [Function.comp_apply,tail_integral μ f hf p hp K (i+1)] using ht

lemma masked_initial_entropy (f : Ω → Ω) (p : Ω → ι) (hf : Measurable f) (hp : Measurable p)
    (A R : Finset ι) (hAR : A⊆R) :
    Entropy.obs μ (maskedState A R f p 0)≤Real.log ((A.card : ℝ)+1) := by
  let g : Option A → Option R := Option.map (fun a => ⟨a.val,hAR a.property⟩)
  have he : maskedState A R f p 0=g ∘ (truncate A ∘ p) := by
    funext x
    by_cases hx : p x∈A
    · simp only [maskedState,hx,↓reduceIte,Function.iterate_zero,Function.id_def,Function.comp_apply,
        truncate_some A _ hx,truncate_some R _ (hAR hx),g,Option.map_some]
    · simp only [maskedState,hx,↓reduceIte,Function.comp_apply,(truncate_none_iff A _).mpr hx,g,Option.map_none]
  have hg : Measurable (g ∘ (truncate A ∘ p)) := by rw [←he]; exact measurable_maskedState A R f p hf hp 0
  rw [he]
  have hh := Entropy.obs_factor μ (truncate A ∘ p) g ((measurable_truncate A).comp hp) hg
  apply hh.trans
  have hb := Entropy.obs_bound μ (truncate A ∘ p) ((measurable_truncate A).comp hp)
  simpa only [Fintype.card_option,Fintype.card_coe,Nat.cast_add,Nat.cast_one] using hb

lemma masked_history_entropy_upper (f : Ω → Ω) (hf : MeasurePreserving f μ μ) (p : Ω → ι) (hp : Measurable p)
    (S : ι → Finset ι) (hS : ∀ᵐ x ∂μ,p (f x)∈S (p x)) {D : ℕ} (hD : 0<D)
    (hcard : ∀ a,(S a).card≤D) (A K : Finset ι) (N : ℕ) :
    Entropy.obs μ (Entropy.history (maskedState A (reach S A N) f p) (N+1))≤
      Entropy.obs μ (Entropy.word f (truncate K ∘ p) (N+1))+Real.log ((A.card : ℝ)+1)+
        (N : ℝ)*((μ {x | p x∉K}).toReal*Real.log (D : ℝ)) := by
  let R : ℕ → (Fin (N+1)→Option K) → Option K := fun i v => if h : i<N+1 then v ⟨i,h⟩ else none
  have hh := Entropy.obs_history_markov μ (maskedState A (reach S A N) f p)
    (measurable_maskedState A _ f p hf.measurable hp)
    (Entropy.word f (truncate K ∘ p) (N+1))
    (Entropy.word_measurable f hf.measurable (truncate K ∘ p) ((measurable_truncate K).comp hp) (N+1)) R N
  have hsum : (∑ i∈Finset.range N,Entropy.cond μ (maskedState A (reach S A N) f p (i+1))
      (fun x => (R (i+1) (Entropy.word f (truncate K ∘ p) (N+1) x),maskedState A (reach S A N) f p i x)))≤
      (N : ℝ)*((μ {x | p x∉K}).toReal*Real.log (D : ℝ)) := by
    calc
      _ ≤ ∑ _i∈Finset.range N,(μ {x | p x∉K}).toReal*Real.log (D : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiN : i<N := Finset.mem_range.mp hi
        simpa only [R,dite_eq_left (show i+1<N+1 by omega),Entropy.word,Function.comp_apply] using
          masked_cond_le_tail μ f hf p hp S hS hD hcard A K N i (by omega)
      _ = _ := by simp
  have hinit := masked_initial_entropy μ f p hf.measurable hp A (reach S A N) (base_subset_reach S A N)
  exact hh.trans (add_le_add (add_le_add le_rfl hinit) hsum)

end StandardMapEntropy.LocalCoding

end
end

end OAI
