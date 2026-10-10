import OAI.Probability.FKMaps.PieceLaws

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def leftCutDensity (P : Parameters) : ℝ := (Stationary.seqLaw (shortLeftLaw P) {x | leftCutAt x 0}).toReal
lemma leftCutDensity_pos (P : Parameters) : 0<leftCutDensity P :=
  ENNReal.toReal_pos (ne_of_gt (leftCutAt_positive P)) (measure_ne_top _ _)
lemma leftCut_density (P : Parameters) :
    ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),
      Tendsto (fun n => (CutOutput.count (fun k => leftCutAt x (k:ℤ)) n:ℝ)/(n:ℝ)) atTop (𝓝 (leftCutDensity P)) := by
  let f : (ℤ → List Letter) → ℝ := fun x => if leftCutAt x 0 then 1 else 0
  have hf : Measurable f := Measurable.ite (leftCutAt_measurable 0) measurable_const measurable_const
  have hi : Integrable f (Stationary.seqLaw (shortLeftLaw P)) := by
    apply (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
    filter_upwards [] with x
    dsimp [f]
    split_ifs <;> norm_num
  have he : (∫ x,f x ∂Stationary.seqLaw (shortLeftLaw P))=leftCutDensity P := by
    simpa only [f,Set.indicator,Pi.one_apply,Measure.real,Set.mem_ofPred_eq,leftCutDensity] using
      integral_indicator_one (μ := Stationary.seqLaw (shortLeftLaw P)) (s := {x | leftCutAt x 0}) (leftCutAt_measurable 0)
  have hh := Stationary.iid_shift_strong_law (shortLeftLaw P) hf hi
  filter_upwards [hh] with x hx
  simpa only [CutOutput.countReal,Stationary.average,Stationary.shift_iterate,f,leftCutAt_shift,zero_add,he] using hx

def forwardTypeSum (x : ℤ → List Letter) (b : Bool) (n : ℕ) : ℝ :=
  ∑ j∈Finset.range n,(typeNet b (x j):ℝ)
lemma left_type_averages (P : Parameters) (b : Bool) :
    ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),
      Tendsto (fun n => forwardTypeSum x b n/(n:ℝ)) atTop (𝓝 (1/2)) := by
  have hh := iid_piece_averages (shortLeftLaw P) (shortLeftLaw_typeNet_integrable P b)
  rw [shortLeftLaw_typeNet_mean] at hh
  exact (futurePieces_preserving (shortLeftLaw P)).quasiMeasurePreserving.ae hh

def leftBurgers (x : ℤ → List Letter) (a : ℤ) (n : ℕ) : List Bool := (reduce (intervalWord x a n)).burgers
lemma leftBurgers_length {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum=1)
    (a : ℤ) (n : ℕ) (ha : leftCutAt x a) : (leftBurgers x a n).length=n := by
  have he := reduce_imbalance (intervalWord x a n)
  rw [imbalance,ha n,intervalWord_net x a n 1 hd] at he
  simp only [List.length_nil,Nat.cast_zero,sub_zero,mul_one] at he
  exact_mod_cast he
lemma leftBurgers_append {x : ℤ → List Letter} {g h : ℕ} (hgh : g≤h) (hg : leftCutAt x g) :
    leftBurgers x 0 h=leftBurgers x g (h-g)++leftBurgers x 0 g := by
  have hh : h=g+(h-g) := by omega
  rw [hh,leftBurgers,intervalWord_add]
  have he : (0:ℤ)+(g:ℤ)=g := zero_add _
  rw [he,reduce_append_no_orders _ _ (hg (h-g))]
  simp only [Nat.add_sub_cancel_left]
  rfl
lemma forwardTypeSum_burgers {x : ℤ → List Letter} (hf : ∀ j,FixedWord (x j))
    (h0 : leftCutAt x 0) (g : ℕ) (b : Bool) :
    forwardTypeSum x b g=((leftBurgers x 0 g).count b:ℝ) := by
  have hh := burger_count_eq_typeNet (intervalWord_fixed hf 0 g) (h0 g) b
  rw [typeNet_intervalWord] at hh
  simp only [zero_add] at hh
  dsimp only [forwardTypeSum,leftBurgers]
  exact_mod_cast hh.symm

def bottomBurgerCount (x : ℤ → List Letter) (b : Bool) (h k : ℕ) : ℕ :=
  (bottom (leftBurgers x 0 h) k).count b
lemma bottomBurgerCount_bounds {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum=1)
    (hf : ∀ j,FixedWord (x j)) (h0 : leftCutAt x 0) {g k h : ℕ} (hg : leftCutAt x g)
    (hgk : g≤k) (hkh : k≤h) (b : Bool) :
    forwardTypeSum x b g ≤ (bottomBurgerCount x b h k:ℝ) ∧
      (bottomBurgerCount x b h k:ℝ) ≤ forwardTypeSum x b g+((k-g:ℕ):ℝ) := by
  have hv : (leftBurgers x 0 g).length=g := leftBurgers_length hd _ _ h0
  have hu : (leftBurgers x g (h-g)).length=h-g := leftBurgers_length hd _ _ hg
  have hb := bottom_append_bounds b (u := leftBurgers x g (h-g)) (v := leftBurgers x 0 g)
    (k := k) (by simpa only [hv] using hgk) (by rw [hu,hv]; omega)
  rw [hv] at hb
  rw [forwardTypeSum_burgers hf h0 g b]
  simp only [bottomBurgerCount,leftBurgers_append (hgk.trans hkh) hg]
  exact ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2⟩

/-- Source uniform bottom counts, for genuine shortened +1 pieces. -/
theorem left_uniform_counts (P : Parameters) (b : Bool) :
    ∀ᵐ x ∂Stationary.seqLaw (shortLeftLaw P),leftCutAt x 0 →
      ∀ ε>0,∀ᶠ k : ℕ in atTop,∀ h≥k,
        |(bottomBurgerCount x b h k:ℝ)/(k:ℝ)-1/2|<ε := by
  filter_upwards [leftSeq_net P,leftSeq_fixed P,leftCut_density P,left_type_averages P b] with x hd hf hc ho
  intro h0 ε hε
  let C : ℕ → Prop := fun k => leftCutAt x (k:ℤ)
  let g : ℕ → ℕ := CutOutput.last C
  have hδ := leftCutDensity_pos P
  have hgdiv := CutOutput.last_div C hδ hc
  have hgap := CutOutput.last_gap_div C hδ hc
  have hgt : Tendsto g atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(CutOutput.last_tendsto C hδ hc).eventually (eventually_ge_atTop (b+1))] with n hn
    change b ≤ CutOutput.last C n
    omega
  have hh := (ho.comp hgt).mul hgdiv
  simp only [mul_one] at hh
  have hsum : Tendsto (fun k => forwardTypeSum x b (g k)/(k:ℝ)) atTop (𝓝 (1/2)) := by
    apply hh.congr'
    filter_upwards [hgt.eventually (eventually_ne_atTop (0:ℕ))] with k hk
    dsimp only [Function.comp_apply,Pi.mul_apply]
    change (forwardTypeSum x b (g k)/(g k:ℝ))*((g k:ℝ)/(k:ℝ))=_
    have hp : (g k:ℝ)≠0 := Nat.cast_ne_zero.mpr hk
    field_simp
  have hlow := (tendsto_order.mp hsum).1 (1/2-ε) (by linarith)
  have hup := (tendsto_order.mp (hsum.add hgap)).2 (1/2+ε) (by linarith)
  filter_upwards [hlow,hup,eventually_gt_atTop (0:ℕ)] with k hl hu hk
  intro h hkh
  have hg0 : C 0 := by simpa [C] using h0
  have hbounds := bottomBurgerCount_bounds hd hf h0 (CutOutput.last_spec hg0 k) (CutOutput.last_le C k) hkh b
  have hkpos : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hl' := (div_le_div_iff_of_pos_right hkpos).mpr hbounds.1
  have hu' := (div_le_div_iff_of_pos_right hkpos).mpr hbounds.2
  rw [add_div] at hu'
  apply abs_lt.mpr
  constructor <;> linarith
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def backwardOutputSum (x : ℤ → List Letter) (o : Order) (n : ℕ) : ℝ :=
  ∑ j∈Finset.range n,if rightOutput x (-1-j)=o then (1:ℝ) else 0
lemma backwardOutputSum_eq {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum= -1)
    (h0 : rightCutAt x 0) {g : ℕ} (hg : rightCutAt x (-(g:ℤ))) (o : Order) :
    backwardOutputSum x o g=((rightOrders x (-g) g).count o:ℝ) := by
  classical
  have hs := rightOutput_segment hd (-(g:ℤ)) g hg (by simpa using h0)
  rw [← hs,count_ofFn_real]
  suffices hsum : backwardOutputSum x o g=∑ j∈Finset.range g,if rightOutput x (-(g:ℤ)+(j:ℤ))=o then (1:ℝ) else 0 by
    calc
      _ = _ := hsum
      _ = _ := by
        convert (Fin.sum_univ_eq_sum_range (fun j => if rightOutput x (-(g:ℤ)+(j:ℤ))=o then (1:ℝ) else 0) g).symm using 1
        apply Finset.sum_congr rfl
        intro j hj
        split_ifs <;> rfl
  unfold backwardOutputSum
  rw [← Finset.sum_range_reflect (fun j => if rightOutput x (-1-(j:ℤ))=o then (1:ℝ) else 0) g]
  apply Finset.sum_congr rfl
  intro j hj
  have he : -1-((g-1-j:ℕ):ℤ)= -(g:ℤ)+(j:ℤ) := by have := Finset.mem_range.mp hj; omega
  rw [he]

def terminalOrderCount (x : ℤ → List Letter) (o : Order) (h k : ℕ) : ℕ :=
  (bottom (rightOrders x (-(h:ℤ)) h) k).count o
lemma terminalOrderCount_bounds {x : ℤ → List Letter} (hd : ∀ j,((x j).map Letter.increment).sum= -1)
    (h0 : rightCutAt x 0) {g k h : ℕ} (hg : rightCutAt x (-(g:ℤ))) (hgk : g≤k) (hkh : k≤h) (o : Order) :
    backwardOutputSum x o g ≤ (terminalOrderCount x o h k:ℝ) ∧
      (terminalOrderCount x o h k:ℝ) ≤ backwardOutputSum x o g+((k-g:ℕ):ℝ) := by
  have hm : rightCutAt x (-(h:ℤ)+(h-g:ℕ)) := by
    have he : -(h:ℤ)+((h-g:ℕ):ℤ)= -(g:ℤ) := by omega
    rwa [he]
  have he : -(h:ℤ)+((h-g:ℕ):ℤ)= -(g:ℤ) := by omega
  have hh : h=(h-g)+g := by omega
  have ha := rightOrders_append (x := x) (-(h:ℤ)) (h-g) g hm
  rw [← hh,he] at ha
  have hv : (rightOrders x (-(g:ℤ)) g).length=g := rightOrders_length hd _ _ (by simpa using h0)
  have hu : (rightOrders x (-(h:ℤ)) (h-g)).length=h-g := rightOrders_length hd _ _ hm
  have hb := bottom_append_bounds o (u := rightOrders x (-(h:ℤ)) (h-g)) (v := rightOrders x (-(g:ℤ)) g)
    (k := k) (by simpa only [hv] using hgk) (by rw [hu,hv]; omega)
  rw [hv] at hb
  rw [backwardOutputSum_eq hd h0 hg o]
  simp only [terminalOrderCount,ha]
  exact ⟨by exact_mod_cast hb.1,by exact_mod_cast hb.2⟩

/-- Uniform terminal counts on the actual R-cut event; the h variable is
unbounded and is not fixed before the limit. -/
theorem right_uniform_counts (P : Parameters) (o : Order) :
    ∀ᵐ x ∂Stationary.seqLaw (rightLaw P),rightCutAt x 0 →
      ∀ ε>0,∀ᶠ k : ℕ in atTop,∀ h≥k,
        |(terminalOrderCount x o h k:ℝ)/(k:ℝ)-outputMass P o|<ε := by
  filter_upwards [rightSeq_net P,rightCut_reverse_density P,rightOutput_reverse_frequencies P o] with x hd hc ho
  intro h0 ε hε
  let C : ℕ → Prop := fun k => rightCutAt x (-(k:ℤ))
  let g : ℕ → ℕ := CutOutput.last C
  have hδ := rightCutDensity_pos P
  have hgdiv := CutOutput.last_div C hδ hc
  have hgap := CutOutput.last_gap_div C hδ hc
  have hgt : Tendsto g atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(CutOutput.last_tendsto C hδ hc).eventually (eventually_ge_atTop (b+1))] with n hn
    change b ≤ CutOutput.last C n
    omega
  have hh := (ho.comp hgt).mul hgdiv
  simp only [mul_one] at hh
  have hsum : Tendsto (fun k => backwardOutputSum x o (g k)/(k:ℝ)) atTop (𝓝 (outputMass P o)) := by
    apply hh.congr'
    filter_upwards [hgt.eventually (eventually_ne_atTop (0:ℕ))] with k hk
    dsimp only [Function.comp_apply,Pi.mul_apply]
    change (backwardOutputSum x o (g k)/(g k:ℝ))*((g k:ℝ)/(k:ℝ))=_
    have hp : (g k:ℝ)≠0 := Nat.cast_ne_zero.mpr hk
    field_simp
  have hlow := (tendsto_order.mp hsum).1 (outputMass P o-ε) (by linarith)
  have hup := (tendsto_order.mp (hsum.add hgap)).2 (outputMass P o+ε) (by linarith)
  filter_upwards [hlow,hup,eventually_gt_atTop (0:ℕ)] with k hl hu hk
  intro h hkh
  have hg0 : C 0 := by simpa [C] using h0
  have hbounds := terminalOrderCount_bounds hd h0 (CutOutput.last_spec hg0 k) (CutOutput.last_le C k) hkh o
  have hkpos : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hl' := (div_le_div_iff_of_pos_right hkpos).mpr hbounds.1
  have hu' := (div_le_div_iff_of_pos_right hkpos).mpr hbounds.2
  rw [add_div] at hu'
  apply abs_lt.mpr
  constructor
  · linarith
  · linarith
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

lemma outputMass_nonneg (P : Parameters) (o : Order) : 0≤outputMass P o := by
  rw [outputMass_eq_measure]
  exact ENNReal.toReal_nonneg
lemma seam_alpha (P : Parameters) : ∃ α : ℝ,0<α ∧ α<1/2 ∧ ∀ b : Bool,outputMass P (some b)<α := by
  have hpos := outputMass_flexible_pos P
  have hnon := outputMass_nonneg P (some false)
  have hf := outputMass_fixed P false
  obtain ⟨α,hα₁,hα₂⟩ := exists_between (show outputMass P (some false)<1/2 by linarith)
  refine ⟨α,lt_of_le_of_lt hnon hα₁,hα₂,?_⟩
  intro b
  rw [outputMass_fixed P b,← outputMass_fixed P false]
  exact hα₁

def GoodLeft (α : ℝ) (B : ℕ) (x : ℤ → List Letter) : Prop :=
  leftCutAt x 0 ∧ ∀ h k : ℕ,B≤k → k≤h → ∀ b : Bool,α*(k:ℝ)≤bottomBurgerCount x b h k
def GoodRight (α : ℝ) (B : ℕ) (x : ℤ → List Letter) : Prop :=
  rightCutAt x 0 ∧ ∀ h k : ℕ,B≤k → k≤h → ∀ b : Bool,(terminalOrderCount x (some b) h k:ℝ)≤α*(k:ℝ)
lemma GoodLeft.mono {α : ℝ} {B D : ℕ} (hBD : B≤D) {x : ℤ → List Letter} (hx : GoodLeft α B x) : GoodLeft α D x :=
  ⟨hx.1,fun h k hk hh b => hx.2 h k (hBD.trans hk) hh b⟩
lemma GoodRight.mono {α : ℝ} {B D : ℕ} (hBD : B≤D) {x : ℤ → List Letter} (hx : GoodRight α B x) : GoodRight α D x :=
  ⟨hx.1,fun h k hk hh b => hx.2 h k (hBD.trans hk) hh b⟩

lemma exists_measure_pos_of_ae_cover {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : Set Ω} {S : ℕ → Set Ω} (hA : 0<μ A) (hcover : ∀ᵐ x ∂μ,x∈A → ∃ n,x∈S n) :
    ∃ n,0<μ (S n) := by
  have hs : A ≤ᵐ[μ] ⋃ n,S n := by
    filter_upwards [hcover] with x hx
    exact fun ha => Set.mem_iUnion.mpr (hx ha)
  have hp : 0<μ (⋃ n,S n) := hA.trans_le (measure_mono_ae hs)
  exact exists_measure_pos_of_not_measure_iUnion_null hp.ne'

lemma goodLeft_positive (P : Parameters) {α : ℝ} (hα : α<1/2) :
    ∃ B,0<Stationary.seqLaw (shortLeftLaw P) {x | GoodLeft α B x} := by
  apply exists_measure_pos_of_ae_cover (Stationary.seqLaw (shortLeftLaw P)) (leftCutAt_positive P)
  filter_upwards [left_uniform_counts P false,left_uniform_counts P true] with x hx₀ hx₁
  intro h0
  have he : 0<1/2-α := by linarith
  have hh := (hx₀ h0 (1/2-α) he).and (hx₁ h0 (1/2-α) he)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N+1,h0,?_⟩
  intro h k hk hkh b
  have hm : |(bottomBurgerCount x b h k:ℝ)/(k:ℝ)-1/2|<1/2-α := by
    cases b
    · exact (hN k (by omega)).1 h hkh
    · exact (hN k (by omega)).2 h hkh
  have hp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hl : α<(bottomBurgerCount x b h k:ℝ)/(k:ℝ) := by have := (abs_lt.mp hm).1; linarith
  exact ((lt_div_iff₀ hp).mp hl).le
lemma goodRight_positive (P : Parameters) {α : ℝ} (hα : ∀ b : Bool,outputMass P (some b)<α) :
    ∃ B,0<Stationary.seqLaw (rightLaw P) {x | GoodRight α B x} := by
  apply exists_measure_pos_of_ae_cover (Stationary.seqLaw (rightLaw P)) (rightCutAt_positive P)
  filter_upwards [right_uniform_counts P (some false),right_uniform_counts P (some true)] with x hx₀ hx₁
  intro h0
  have hε (b : Bool) : 0<α-outputMass P (some b) := sub_pos.mpr (hα b)
  have hh := (hx₀ h0 (α-outputMass P (some false)) (hε false)).and
    (hx₁ h0 (α-outputMass P (some true)) (hε true))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  refine ⟨N+1,h0,?_⟩
  intro h k hk hkh b
  have hm : |(terminalOrderCount x (some b) h k:ℝ)/(k:ℝ)-outputMass P (some b)|<α-outputMass P (some b) := by
    cases b
    · exact (hN k (by omega)).1 h hkh
    · exact (hN k (by omega)).2 h hkh
  have hp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hu : (terminalOrderCount x (some b) h k:ℝ)/(k:ℝ)<α := by have := (abs_lt.mp hm).2; linarith
  exact ((div_lt_iff₀ hp).mp hu).le

lemma intervalWord_measurable_coords {S : Set ℤ} (a : ℤ) (n : ℕ)
    (hS : ∀ j<n,a+(j:ℤ)∈S) : Measurable[Stationary.coords (α := List Letter) S] (fun x => intervalWord x a n) := by
  let : MeasurableSpace (ℤ → List Letter) := Stationary.coords S
  have hf : Measurable (fun x : ℤ → List Letter => (fun j : Fin n => x (a+j))) := by
    apply Measurable.of_eval
    intro j
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le (a+j) (le_iSup_of_le (hS j j.isLt) le_rfl)
  have he : (fun x : ℤ → List Letter => intervalWord x a n)=fun x => (List.ofFn (fun j : Fin n => x (a+j))).flatten := by
    funext x
    exact piecesPrefix_ofFn _ _
  rw [he]
  exact (measurable_of_countable (fun w : Fin n → List Letter => (List.ofFn w).flatten)).comp hf
lemma goodLeft_measurable (α : ℝ) (B : ℕ) : MeasurableSet {x | GoodLeft α B x} := by
  simp only [GoodLeft,Set.ofPred_and,Set.ofPred_forall]
  apply (leftCutAt_measurable 0).inter
  apply MeasurableSet.iInter
  intro h
  exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _hk => MeasurableSet.iInter (fun _hh =>
    MeasurableSet.iInter (fun b => (intervalWord_measurable 0 h) ((Set.to_countable {w : List Letter |
      α*(k:ℝ)≤((bottom (reduce w).burgers k).count b:ℝ)}).measurableSet)))))
lemma goodRight_past_measurable (α : ℝ) (B : ℕ) :
    MeasurableSet[Stationary.coords (α := List Letter) {j | j<0}] {x | GoodRight α B x} := by
  simp only [GoodRight,Set.ofPred_and,Set.ofPred_forall]
  apply rightCutAt_zero_past_measurable.inter
  apply MeasurableSet.iInter
  intro h
  have hm := intervalWord_measurable_coords (S := {j | j<0}) (-(h:ℤ)) h (fun j hj => by change -(h:ℤ)+j<0; omega)
  exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _hk => MeasurableSet.iInter (fun _hh =>
    MeasurableSet.iInter (fun b => hm ((Set.to_countable {w : List Letter |
      ((bottom (reduce w).orders k).count (some b):ℝ)≤α*(k:ℝ)}).measurableSet)))))
lemma goodRight_measurable (α : ℝ) (B : ℕ) : MeasurableSet {x | GoodRight α B x} :=
  (Stationary.coords_le _) _ (goodRight_past_measurable α B)
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

def FlexiblePrefix (x : ℤ → List Letter) (D : ℕ) : Prop :=
  ∀ j : ℕ,j<D → x j=[Letter.order none]
lemma intervalWord_flexible {x : ℤ → List Letter} {D n : ℕ} {a : ℤ}
    (hx : FlexiblePrefix x D) (ha : 0≤a) (hn : a+n≤D) :
    intervalWord x a n=List.replicate n (Letter.order none) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [intervalWord_succ,ih (by omega),show x (a+n)=[Letter.order none] by
      have he : a+(n:ℤ)=((a+n).toNat:ℤ) := by rw [Int.toNat_of_nonneg (by omega)]
      rw [he]
      exact hx _ (by omega)]
    simp only [List.replicate_succ']
lemma reduce_flexible (n : ℕ) : reduce (List.replicate n (Letter.order none))=⟨List.replicate n none,[]⟩ := by
  have hh := evalOrders_empty (List.replicate n none)
  simpa only [evalOrders,reduce,List.map_replicate] using hh
lemma forcedRight_shape {x : ℤ → List Letter} {D h : ℕ}
    (hc : rightCutAt x 0) (hx : FlexiblePrefix x D) :
    reduce (intervalWord x ((D:ℤ)-h) h)=
      if h≤D then ⟨List.replicate h none,[]⟩ else
        ⟨rightOrders x (-(h-D:ℕ):ℤ) (h-D)++List.replicate D none,[]⟩ := by
  split_ifs with hh
  · rw [intervalWord_flexible hx (by omega) (by omega),reduce_flexible]
  · have he : h=(h-D)+D := by omega
    have hs : (D:ℤ)-h=-(h-D:ℕ) := by omega
    rw [hs]
    conv_lhs => arg 1; arg 3; rw [he]
    rw [intervalWord_add]
    have hi : -(h-D:ℕ)+(h-D:ℕ)= (0:ℤ) := by omega
    rw [hi,reduce_append_no_burgers _ _ (by simpa using hc (h-D)),
      intervalWord_flexible (a := 0) (n := D) hx (by omega) (by omega),reduce_flexible]
    rfl
lemma count_bottom_flexible (b : Bool) (n k : ℕ) :
    (bottom (List.replicate n (none : Order)) k).count (some b)=0 := by
  simp [bottom,List.drop_replicate,List.count_replicate]
lemma count_bottom_flexible_append (b : Bool) (u : List Order) {D k : ℕ} (hk : D≤k) :
    (bottom (u++List.replicate D none) k).count (some b)=(bottom u (k-D)).count (some b) := by
  rw [bottom_append (by simpa using hk),List.count_append]
  simp [List.count_replicate]
lemma count_bottom_flexible_append_small (b : Bool) (u : List Order) {D k : ℕ} (hk : k≤D) :
    (bottom (u++List.replicate D none) k).count (some b)=0 := by
  unfold bottom
  rw [List.length_append,List.length_replicate,List.drop_append,
    List.drop_eq_nil_of_le (by omega : u.length ≤ u.length+D-k)]
  simp [List.drop_replicate,List.count_replicate]

/-- Deterministic source seam criterion, including every small k. -/
theorem seam_matching {x y : ℤ → List Letter} {α : ℝ} {B D h : ℕ}
    (hα : 0≤α) (hBD : B≤D) (hD : (B:ℝ)≤α*D)
    (hl : GoodLeft α B x) (hr : GoodRight α B y) (hf : FlexiblePrefix y D)
    (hdl : ∀ j,((x j).map Letter.increment).sum=1)
    (hdr : ∀ j,((y j).map Letter.increment).sum= -1) :
    EmptyReducing (intervalWord x 0 h++intervalWord y ((D:ℤ)-h) h) := by
  have hlb : (leftBurgers x 0 h).length=h := leftBurgers_length hdl _ _ hl.1
  have hro : (reduce (intervalWord y ((D:ℤ)-h) h)).orders.length=h := by
    have hi := reduce_imbalance (intervalWord y ((D:ℤ)-h) h)
    rw [imbalance,intervalWord_net y _ h (-1) hdr,forcedRight_shape hr.1 hf] at hi
    split_ifs at hi ⊢ with hh
    · simp only [List.length_replicate,forcedRight_shape hr.1 hf,ite_eq_left hh]
    · rw [forcedRight_shape hr.1 hf,ite_eq_right hh]
      change ((rightOrders y (-(h-D:ℕ):ℤ) (h-D)++List.replicate D none)).length=h
      simp only [List.length_nil,Nat.cast_zero,zero_sub,mul_neg_one] at hi
      omega
  have hno : (reduce (intervalWord y ((D:ℤ)-h) h)).burgers=[] := by
    rw [forcedRight_shape hr.1 hf]
    split_ifs <;> rfl
  have hs : SupplyCondition (leftBurgers x 0 h) (reduce (intervalWord y ((D:ℤ)-h) h)).orders := by
    refine ⟨hlb.trans hro.symm,?_⟩
    intro k hk b
    rw [hro] at hk
    rw [forcedRight_shape hr.1 hf]
    by_cases hh : h≤D
    · rw [ite_eq_left hh,count_bottom_flexible]
      exact Nat.zero_le _
    rw [ite_eq_right hh]
    by_cases hkd : k≤D
    · rw [count_bottom_flexible_append_small b _ hkd]
      exact Nat.zero_le _
    rw [count_bottom_flexible_append b _ (by omega)]
    have hkB : B≤k := by omega
    have hlc := hl.2 h k hkB hk b
    have hrc : ((bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D)).count (some b):ℝ)≤α*k := by
      by_cases hkb : B≤k-D
      · have hh' := hr.2 (h-D) (k-D) hkb (by omega) b
        change ((bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D)).count (some b):ℝ)≤α*(k-D:ℕ) at hh'
        exact hh'.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (show k-D≤k by omega)) hα)
      · have hc := List.count_le_length (a := some b) (l := bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D))
        have hlen : (bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D)).length≤k-D := by
          simp only [bottom,List.length_drop]; omega
        have hb : ((bottom (rightOrders y (-(h-D:ℕ):ℤ) (h-D)) (k-D)).count (some b):ℝ)≤B := by
          exact_mod_cast (hc.trans (hlen.trans (by omega)))
        exact hb.trans (hD.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast (show D≤k by omega)) hα))
    exact_mod_cast hrc.trans hlc
  have hm := matching_of_supplyCondition hs
  unfold EmptyReducing reduce
  rw [run_append]
  have he : run (intervalWord x 0 h) ⟨[],[]⟩=⟨[],leftBurgers x 0 h⟩ := by
    change reduce (intervalWord x 0 h)=_
    have hh := hl.1 h
    cases he : reduce (intervalWord x 0 h)
    simp_all only [leftBurgers]
  rw [he,run_older_supply,hm,hno]
  rfl
end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Inventory
open Classical

lemma flexiblePrefix_future_measurable (D : ℕ) :
    MeasurableSet[Stationary.coords (α := List Letter) {j | 0≤j}] {x | FlexiblePrefix x D} := by
  simp only [FlexiblePrefix,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _hj
  have hm : Measurable[Stationary.coords (α := List Letter) {j | 0≤j}] (fun x : ℤ → List Letter => x j) := by
    apply measurable_iff_comap_le.mpr
    exact le_iSup_of_le (j:ℤ) (le_iSup_of_le (show (0:ℤ)≤j by omega) le_rfl)
  exact hm (measurableSet_singleton _)
lemma flexiblePrefix_measurable (D : ℕ) : MeasurableSet {x | FlexiblePrefix x D} :=
  (Stationary.coords_le _) _ (flexiblePrefix_future_measurable D)
lemma flexiblePrefix_positive (P : Parameters) (D : ℕ) :
    0<Stationary.seqLaw (rightLaw P) {x | FlexiblePrefix x D} := by
  have he : {x | FlexiblePrefix x D}=futurePieces ⁻¹' pieceCylinder (List.replicate D [Letter.order none]) := by
    ext x
    simp only [FlexiblePrefix,Set.mem_ofPred_eq,Set.mem_preimage,pieceCylinder]
    constructor
    · intro h j
      simpa [futurePieces] using h j (by simpa using j.isLt)
    · intro h j hj
      simpa [futurePieces] using h ⟨j,by simpa using hj⟩
  rw [he,(futurePieces_preserving (rightLaw P)).measure_preimage (pieceCylinder_measurable _).nullMeasurableSet]
  apply pieceCylinder_positive
  intro w hw
  have he : w=[Letter.order none] := (List.mem_replicate.mp hw).2
  subst w
  exact rightLaw_order_positive P none
lemma goodRight_forced_positive (P : Parameters) {α : ℝ} {B D : ℕ}
    (hR : 0<Stationary.seqLaw (rightLaw P) {x | GoodRight α B x}) :
    0<Stationary.seqLaw (rightLaw P) {x | GoodRight α B x ∧ FlexiblePrefix x D} := by
  have hi := Stationary.indep_coords (rightLaw P) (S := {j | j<0}) (R := {j | 0≤j})
    (Set.disjoint_left.mpr (fun j hj hj' => by change j<0 at hj; change 0≤j at hj'; omega))
  have he := ((indep_iff_forall_indepSet _).mp hi _ _ (goodRight_past_measurable α B)
    (flexiblePrefix_future_measurable D)).measure_inter_eq_mul
  change Stationary.seqLaw (rightLaw P) ({x | GoodRight α B x}∩{x | FlexiblePrefix x D})>0
  rw [he]
  exact ENNReal.mul_pos_iff.mpr ⟨hR,flexiblePrefix_positive P D⟩

def piecesFrom (a : ℤ) (x : ℤ → List Letter) : ℕ → List Letter := fun j => x (a+j)
lemma piecesFrom_preserving (ν : Measure (List Letter)) [IsProbabilityMeasure ν] (a : ℤ) :
    MeasurePreserving (piecesFrom a) (Stationary.seqLaw ν) (naturalPiecesLaw ν) := by
  refine ⟨Measurable.of_eval (fun index => measurable_pi_apply (a+index)),?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun j k h => Int.ofNat_inj.mp (add_left_cancel h))

def pieceSeamEvent (h : ℕ) : Set ((ℕ → List Letter) × (ℕ → List Letter)) :=
  {z | EmptyReducing (piecesPrefix z.1 h++piecesPrefix z.2 h)}
lemma pieceSeamEvent_measurable (h : ℕ) : MeasurableSet (pieceSeamEvent h) := by
  have hm := ((measurable_of_countable (fun z : List Letter×List Letter => z.1++z.2)).comp
    (((piecesPrefix_measurable h).comp measurable_fst).prodMk ((piecesPrefix_measurable h).comp measurable_snd)))
  exact hm ((Set.to_countable {w | EmptyReducing w}).measurableSet)

/-- Uniform success for the actual independent shortened-L and genuine-R laws.
Raw stopping-word transport is separate: no finite stopping-length mean is used. -/
theorem piece_seam_uniform (P : Parameters) : ∃ δ : ℝ,0<δ ∧ ∀ h : ℕ,
    ENNReal.ofReal δ≤((naturalPiecesLaw (shortLeftLaw P)).prod (naturalPiecesLaw (rightLaw P))) (pieceSeamEvent h) := by
  obtain ⟨α,hα,hα',hαR⟩ := seam_alpha P
  obtain ⟨B₀,hB₀⟩ := goodLeft_positive P hα'
  obtain ⟨B₁,hB₁⟩ := goodRight_positive P hαR
  let B := max B₀ B₁
  have hL : 0<Stationary.seqLaw (shortLeftLaw P) {x | GoodLeft α B x} :=
    hB₀.trans_le (measure_mono (fun _ hx => hx.mono (Nat.le_max_left _ _)))
  have hR : 0<Stationary.seqLaw (rightLaw P) {x | GoodRight α B x} :=
    hB₁.trans_le (measure_mono (fun _ hx => hx.mono (Nat.le_max_right _ _)))
  obtain ⟨d,hd⟩ := exists_nat_gt ((B:ℝ)/α)
  let D := max B d
  have hBD : B≤D := Nat.le_max_left _ _
  have hD : (B:ℝ)≤α*D := by
    have he : (B:ℝ)<α*d := by have := (div_lt_iff₀ hα).mp hd; nlinarith
    exact he.le.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_max_right B d) hα.le)
  let A : Set (ℤ → List Letter) := {x | GoodLeft α B x}
  let R : Set (ℤ → List Letter) := {x | GoodRight α B x ∧ FlexiblePrefix x D}
  let μ := (Stationary.seqLaw (shortLeftLaw P)).prod (Stationary.seqLaw (rightLaw P))
  have hp : 0<μ (A×ˢR) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos_iff.mpr ⟨hL,goodRight_forced_positive P hR⟩
  refine ⟨(μ (A×ˢR)).toReal,ENNReal.toReal_pos hp.ne' (measure_ne_top _ _),?_⟩
  intro h
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  let F := Prod.map (piecesFrom 0) (piecesFrom ((D:ℤ)-h))
  have hF : MeasurePreserving F μ ((naturalPiecesLaw (shortLeftLaw P)).prod (naturalPiecesLaw (rightLaw P))) :=
    (piecesFrom_preserving (shortLeftLaw P) 0).prod (piecesFrom_preserving (rightLaw P) ((D:ℤ)-h))
  rw [← hF.measure_preimage (pieceSeamEvent_measurable h).nullMeasurableSet]
  apply measure_mono_ae
  have hal : ∀ᵐ z ∂μ,∀ j,((z.1 j).map Letter.increment).sum=1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae (leftSeq_net P)
  have har : ∀ᵐ z ∂μ,∀ j,((z.2 j).map Letter.increment).sum= -1 :=
    measurePreserving_snd.quasiMeasurePreserving.ae (rightSeq_net P)
  filter_upwards [hal,har] with z hl hr
  intro hz
  exact seam_matching hα.le hBD hD hz.1 hz.2.1 hz.2.2 hl hr
end FKCRT.Inventory

end

end OAI
