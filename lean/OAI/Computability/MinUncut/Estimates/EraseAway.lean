import Mathlib
import OAI.Computability.MinUncut.Estimates.FaceUpdateSelf
import OAI.Computability.MinUncut.Estimates.Away

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Subbox
open OuterSmoothness
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]

lemma expect_sigma_const {T : Type*} [Fintype T] {B : T → Type*} [∀ t, Fintype (B t)]
    (D : ℕ) (hD : ∀ t, Fintype.card (B t)=D) (f : (t : T) → B t → ℝ) :
    (𝔼 t, 𝔼 b, f t b)=(𝔼 p : Sigma B, f p.fst p.snd) := by
  have hc : Fintype.card (Sigma B)=Fintype.card T*D := by simp [Fintype.card_sigma,hD]
  simp only [Fintype.expect_eq_sum_div_card,hD,hc,Nat.cast_mul,Fintype.sum_sigma]
  rw [← Finset.sum_div, div_div]
  congr 1
  ring

def eraseAway (x : A) (Y : Finset A) : Finset (Away x) :=
  (Y.erase x).attach.map ⟨fun (a : {a : A // a∈Y.erase x}) => ⟨a.val,(Finset.mem_erase.mp a.property).1⟩,
    fun _ _ h => Subtype.ext (congrArg (fun z : Away x => z.val) h)⟩

omit [Fintype A] in
@[simp] lemma mem_eraseAway (x : A) (Y : Finset A) (a : Away x) :
    a∈eraseAway x Y ↔ a.val∈Y := by
  simp only [eraseAway,Finset.mem_map,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val hb
    rw [← he]
    exact (Finset.mem_erase.mp b.property).2
  · intro ha
    exact ⟨⟨a.val,Finset.mem_erase.mpr ⟨a.property,ha⟩⟩,rfl⟩

omit [Fintype A] in
lemma eraseAway_card (x : A) (Y : Finset A) (hx : x∈Y) :
    (eraseAway x Y).card=Y.card-1 := by simp [eraseAway,Finset.card_erase_of_mem hx]

def unpoint (x : A) {k : ℕ} (Y : FixedSets A (k+1)) (hx : x∈Y.val) : FixedSets (Away x) k :=
  ⟨eraseAway x Y.val,by rw [eraseAway_card x Y.val hx,Y.property]; omega⟩

@[simp] lemma pointed_unpoint (x : A) {k : ℕ} (Y : FixedSets A (k+1)) (hx : x∈Y.val) :
    pointedSet x (unpoint x Y hx)=Y.val := by
  ext a
  by_cases ha : a=x
  · subst a; simp [mem_pointedSet_self,hx]
  · rw [mem_pointedSet ha]
    exact mem_eraseAway x Y.val ⟨a,ha⟩

@[simp] lemma unpoint_pointed (x : A) {k : ℕ} (H : FixedSets (Away x) k) :
    unpoint x ⟨pointedSet x H,pointedSet_card x H⟩ (mem_pointedSet_self x H)=H := by
  apply Subtype.ext
  ext a
  change a∈eraseAway x (pointedSet x H) ↔ a∈H.val
  rw [mem_eraseAway,mem_pointedSet a.property]

abbrev UnpointedBox (ι A : Type*) [Fintype A] (k : ℕ) := ι → FixedSets A (k+1)
abbrev BoxPoint {k : ℕ} (Y : UnpointedBox ι A k) := ∀ i, {a : A // a∈(Y i).val}

def boxOfPointed (x : ι → A) {k : ℕ} (H : PointedBox x k) : UnpointedBox ι A k :=
  fun i => ⟨pointedSet (x i) (H i),pointedSet_card (x i) (H i)⟩

omit [DecidableEq A] [Fintype ι] [DecidableEq ι] in
lemma boxPoint_heq {k : ℕ} {Y Z : UnpointedBox ι A k} (h : Y=Z)
    (x : BoxPoint Y) (y : BoxPoint Z) (he : ∀ i, (x i).val=(y i).val) : HEq x y := by
  subst Z
  apply heq_of_eq
  funext i
  exact Subtype.ext (he i)

def boxJointEquiv (k : ℕ) : (Σ x : ι → A, PointedBox x k) ≃ (Σ Y : UnpointedBox ι A k, BoxPoint Y) where
  toFun p := ⟨boxOfPointed p.fst p.snd, fun i => ⟨p.fst i,mem_pointedSet_self _ _⟩⟩
  invFun p := ⟨fun i => (p.snd i).val, fun i => unpoint (p.snd i).val (p.fst i) (p.snd i).property⟩
  left_inv p := by
    rcases p with ⟨x,H⟩
    dsimp [boxOfPointed]
    congr 1
    funext i
    exact unpoint_pointed (x i) (H i)
  right_inv p := by
    rcases p with ⟨Y,x⟩
    have hY : boxOfPointed (fun i => (x i).val) (fun i => unpoint (x i).val (Y i) (x i).property)=Y := by
      funext i
      apply Subtype.ext
      exact pointed_unpoint (x i).val (Y i) (x i).property
    apply Sigma.ext hY
    exact boxPoint_heq hY _ _ (fun i => rfl)

omit [DecidableEq A] in
lemma card_boxPoint {k : ℕ} (Y : UnpointedBox ι A k) :
    Fintype.card (BoxPoint Y)=(k+1)^Fintype.card ι := by
  simp only [BoxPoint,Fintype.card_pi,Fintype.card_coe]
  simp only [(Y _).property,Finset.prod_const,Finset.card_univ]

lemma card_pointedBox (x : ι → A) (k : ℕ) :
    Fintype.card (PointedBox x k)=((Fintype.card A-1).choose k)^Fintype.card ι := by
  simp only [PointedBox,Fintype.card_pi,FixedSets,Fintype.card_finset_len,card_away,Finset.prod_const,Finset.card_univ]

theorem bayes_box (k : ℕ) (f : UnpointedBox ι A k → (ι → A) → ℝ) :
    (𝔼 x : ι → A, 𝔼 H : PointedBox x k, f (boxOfPointed x H) x) =
      𝔼 Y : UnpointedBox ι A k, 𝔼 x : BoxPoint Y, f Y (fun i => (x i).val) := by
  rw [expect_sigma_const _ (fun x => card_pointedBox x k)]
  rw [expect_sigma_const _ (fun Y => card_boxPoint Y)]
  apply Fintype.expect_equiv (boxJointEquiv (ι := ι) (A := A) k)
  intro p
  rfl
open OuterSmoothness
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

def coordinateEnum {k : ℕ} (Y : UnpointedBox ι A k) (i : ι) :
    Fin (k+1) ≃ {a : A // a∈(Y i).val} :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_fin,Fintype.card_coe,(Y i).property])

def pointEnum {k : ℕ} (Y : UnpointedBox ι A k) : (ι → Fin (k+1)) ≃ BoxPoint Y :=
  Equiv.piCongrRight (coordinateEnum Y)

def pointEmbed {k : ℕ} (Y : UnpointedBox ι A k) (u : ι → Fin (k+1)) : ι → A :=
  fun i => (coordinateEnum Y i (u i)).val

omit [Fintype ι] [DecidableEq ι] [DecidableEq A] in
lemma pointEmbed_injective {k : ℕ} (Y : UnpointedBox ι A k) :
    Function.Injective (pointEmbed Y) := by
  intro u v h
  funext i
  apply (coordinateEnum Y i).injective
  apply Subtype.ext
  exact congrFun h i

omit [Fintype ι] [DecidableEq ι] [DecidableEq A] in
lemma pointEmbed_mem {k : ℕ} (Y : UnpointedBox ι A k) (u : ι → Fin (k+1)) (i : ι) :
    pointEmbed Y u i ∈ (Y i).val := (coordinateEnum Y i (u i)).property

lemma pointwise_bayes {k : ℕ} (hk : k≤Fintype.card A-1) (f : (ι → A) → ℝ) :
    (𝔼 x : ι → A, f x) = 𝔼 Y : UnpointedBox ι A k, 𝔼 u : ι → Fin (k+1), f (pointEmbed Y u) := by
  have (x : ι → A) (i : ι) : Nonempty (FixedSets (Away (x i)) k) :=
    fixedSets_nonempty (by simpa only [card_away] using hk)
  have h := bayes_box (ι := ι) (A := A) k (fun _ x => f x)
  simp only [Fintype.expect_const] at h
  rw [h]
  apply Finset.expect_congr rfl
  intro Y _
  symm
  exact Fintype.expect_equiv (pointEnum Y) _ _ (fun u => rfl)
end MinUncut.Subbox

namespace MinUncut.Inner
open Subbox OuterSmoothness
open scoped BigOperators
variable {m n : ℕ}

def codeRestriction {k : ℕ} (Y : UnpointedBox (Fin m) (Fin n) k) (z : Code m n) : Code m (k+1) :=
  ⟨fun u => z.val (pointEmbed Y u), by
    obtain ⟨b,hb⟩ := z.property
    refine ⟨fun r => b ⟨r.fst,fun i => (coordinateEnum Y i.val (r.snd i)).val⟩,?_⟩
    funext u
    rw [← hb]
    rfl⟩

theorem faceCorrelation_restriction {k : ℕ} (hk : k≤n-1) (v : Point m n → ℝ) :
    faceCorrelation v ≤ 𝔼 Y : UnpointedBox (Fin m) (Fin n) k,
      faceCorrelation (fun u : Point m (k+1) => v (pointEmbed Y u)) := by
  apply faceCorrelation_le
  intro z
  have he := pointwise_bayes (ι := Fin m) (A := Fin n) (by simpa using hk)
    (fun x => v x*BinaryFourier.sign (z.val x))
  rw [he]
  calc
    _ ≤ 𝔼 Y : UnpointedBox (Fin m) (Fin n) k,
      |𝔼 u, v (pointEmbed Y u)*BinaryFourier.sign (z.val (pointEmbed Y u))| :=
        Finset.abs_expect_le _ _
    _ ≤ _ := Finset.expect_le_expect (fun Y _ => code_correlation_le _ (codeRestriction Y z))
end MinUncut.Inner
namespace MinUncut.Slice
open MeasureTheory BinaryFourier
open scoped BigOperators
variable {W Ω : Type*} [Fintype W] [DecidableEq W] [AddCommGroup W] [Module F₂ W]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
local instance eraseAwayDualFintype : Fintype (Module.Dual F₂ W) := BinaryFourier.dualFintype

def energy (v : Ω → W → ℝ) (t : Ω) : ℝ := 𝔼 w, (v t w)^2

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] [MeasurableSpace Ω] in
lemma energy_nonneg (v : Ω → W → ℝ) (t : Ω) : 0 ≤ energy v t :=
  Finset.expect_nonneg (fun _ _ => sq_nonneg _)

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] in
lemma energy_measurable (v : Ω → W → ℝ) (hv : ∀ w, Measurable (fun t => v t w)) :
    Measurable (energy v) := by
  change Measurable (fun t => 𝔼 w, (v t w)^2)
  simp only [Finset.expect_eq_sum_div_card]
  exact (Finset.measurable_sum _ (fun w _ => (hv w).pow_const _)).div_const _

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] [IsProbabilityMeasure μ] in
lemma energy_integrable (v : Ω → W → ℝ) (hv : ∀ w, MemLp (fun t => v t w) 2 μ) :
    Integrable (energy v) μ := by
  change Integrable (fun t => 𝔼 w, (v t w)^2) μ
  simp only [Finset.expect_eq_sum_div_card]
  exact (integrable_finsetSum _ (fun w _ => (hv w).integrable_sq)).div_const _

omit [DecidableEq W] [AddCommGroup W] [Module F₂ W] [IsProbabilityMeasure μ] in
lemma sliceNorm_memLp (v : Ω → W → ℝ) (hm : ∀ w, Measurable (fun t => v t w))
    (hv : ∀ w, MemLp (fun t => v t w) 2 μ) :
    MemLp (fun t => Real.sqrt (energy v t)) 2 μ := by
  apply (memLp_two_iff_integrable_sq ((energy_measurable v hm).sqrt.aestronglyMeasurable)).mpr
  simpa only [Real.sq_sqrt (energy_nonneg v _)] using energy_integrable v hv

omit [DecidableEq W] in
lemma oddMax_measurable (one : W) (v : Ω → W → ℝ)
    (hm : ∀ w, Measurable (fun t => v t w)) :
    Measurable (fun t => oddMax one (v t)) := by
  let fs : Module.Dual F₂ W → Ω → ℝ := fun α t =>
    if α one=1 then |coefficient (v t) α| else 0
  have hs (α : Module.Dual F₂ W) : Measurable (fs α) := by
    by_cases h : α one=1
    · simp only [fs,h,↓reduceIte,coefficient,Finset.expect_eq_sum_div_card]
      exact ((Finset.measurable_sum _ (fun w _ => (hm w).mul_const _)).div_const _).abs
    · simpa only [fs,h,↓reduceIte] using (measurable_const : Measurable (fun _ : Ω => (0:ℝ)))
  have hh : Measurable (Finset.univ.sup' Finset.univ_nonempty fs) :=
    Finset.sup'_induction (p := Measurable) Finset.univ_nonempty fs
      (fun _ hf _ hg => hf.max hg) (fun α _ => hs α)
  convert hh using 1
  funext t
  simp only [Finset.sup'_apply,fs,oddMax]

omit [DecidableEq W] in
lemma oddMax_memLp (one : W) (v : Ω → W → ℝ)
    (hv : ∀ w, MemLp (fun t => v t w) 2 μ) :
    MemLp (fun t => oddMax one (v t)) 2 μ := by
  let fs : Module.Dual F₂ W → Ω → ℝ := fun α t =>
    if α one=1 then |coefficient (v t) α| else 0
  have hs (α : Module.Dual F₂ W) : MemLp (fs α) 2 μ := by
    by_cases h : α one=1
    · simp only [fs,h,↓reduceIte]
      have hh : MemLp (fun t => coefficient (v t) α) 2 μ :=
        RowNoise.memLp_expect _ (fun w => (hv w).mul_const _)
      simpa only [Real.norm_eq_abs] using hh.norm
    · simpa only [fs,h,↓reduceIte] using (memLp_const (0:ℝ) : MemLp (fun _ : Ω => (0:ℝ)) 2 μ)
  have hh : MemLp (Finset.univ.sup' Finset.univ_nonempty fs) 2 μ :=
    Finset.sup'_induction (p := fun f => MemLp f 2 μ) Finset.univ_nonempty fs
      (fun _ hf _ hg => hf.sup hg) (fun α _ => hs α)
  convert hh using 1
  funext t
  simp only [Finset.sup'_apply,fs,oddMax]

omit [DecidableEq W] in
lemma processed_measurable (one : W) (v : Ω → W → ℝ)
    (hm : ∀ w, Measurable (fun t => v t w)) (H γ A : ℝ) (w : W) :
    Measurable (fun t => processed H γ A one (v t) w) := by
  have hd : MeasurableSet {t | H < Real.sqrt (energy v t) ∨ γ < oddMax one (v t)} :=
    (measurableSet_lt measurable_const (energy_measurable v hm).sqrt).union
      (measurableSet_lt measurable_const (oddMax_measurable one v hm))
  exact Measurable.ite hd measurable_const (measurable_const.max ((hm w).min measurable_const))

omit [DecidableEq W] in
lemma processed_memLp (one : W) (v : Ω → W → ℝ)
    (hm : ∀ w, Measurable (fun t => v t w)) {H γ A : ℝ} (hA : 0≤A) (w : W) :
    MemLp (fun t => processed H γ A one (v t) w) 2 μ := by
  exact MemLp.of_bound (processed_measurable one v hm H γ A w).aestronglyMeasurable A
    (Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using processed_abs_le hA one (v t) w))

omit [DecidableEq W] in
theorem processed_integral_loss (one : W) (v : Ω → W → ℝ)
    (hm : ∀ w, Measurable (fun t => v t w)) (hv : ∀ w, MemLp (fun t => v t w) 2 μ)
    {H γ A : ℝ} (hH : 0<H) (hγ : 0<γ) (hA : 0<A) :
    (∫ t, (𝔼 w, |v t w-processed H γ A one (v t) w|) ∂μ) ≤
      (∫ t, energy v t ∂μ)/H +
      Real.sqrt (∫ t, energy v t ∂μ)*Real.sqrt ((∫ t, oddMax one (v t) ∂μ)/γ) +
      (∫ t, energy v t ∂μ)/A := by
  let S := {t : Ω | γ < oddMax one (v t)}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (oddMax_measurable one v hm)
  have he := energy_integrable v hv
  have hn := sliceNorm_memLp v hm hv
  have hq := oddMax_memLp one v hv
  have hi : Integrable (fun t => 𝔼 w, |v t w-processed H γ A one (v t) w|) μ := by
    simp only [Finset.expect_eq_sum_div_card]
    exact (integrable_finsetSum _ (fun w _ =>
      ((hv w).sub (processed_memLp one v hm hA.le w)).integrable (by norm_num) |>.abs)).div_const _
  have hvS : Integrable (S.indicator (fun t => Real.sqrt (energy v t))) μ :=
    (hn.integrable (by norm_num)).indicator hS
  have htail := integral_tail_loss hn (oddMax_measurable one v hm)
    (hq.integrable (by norm_num)) (fun t => oddMax_nonneg one (v t)) hγ
  simp only [abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (energy_nonneg v _)] at htail
  calc
    _ ≤ ∫ t, energy v t/H + S.indicator (fun t => Real.sqrt (energy v t)) t + energy v t/A ∂μ := by
      apply integral_mono hi (((he.div_const _).add hvS).add (he.div_const _))
      intro t
      simp only [Pi.add_apply]
      simpa only [energy,Set.indicator_apply,S,Set.mem_ofPred_eq] using processed_mean_loss hH hA one (v t)
    _ = (∫ t, energy v t ∂μ)/H + (∫ t in S, Real.sqrt (energy v t) ∂μ) + (∫ t, energy v t ∂μ)/A := by
      rw [integral_add, integral_add, integral_div, integral_div, integral_indicator hS]
      · exact he.div_const _
      · exact hvS
      · exact (he.div_const _).add hvS
      · exact he.div_const _
    _ ≤ _ := by change (∫ t in S, Real.sqrt (energy v t) ∂μ) ≤ _ at htail; linarith
end MinUncut.Slice

end

end OAI
