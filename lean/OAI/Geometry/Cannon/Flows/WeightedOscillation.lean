import Mathlib
import OAI.Geometry.Cannon.Flows.Oscillation

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology

namespace CannonMagnification

lemma exists_tail_maximum (f : ℕ → ℝ) (hf : ∀ n, 0 < f n)
    (ht : Tendsto f atTop (𝓝 0)) (n : ℕ) :
    ∃ k, n ≤ k ∧ ∀ l, k ≤ l → f l ≤ f k := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (hf n)))
  let B := max N (n+1)
  have hnB : n ∈ Finset.Ico n B := by simp only [Finset.mem_Ico]; exact ⟨le_rfl,(Nat.lt_succ_self n).trans_le (le_max_right _ _)⟩
  obtain ⟨k,hk,hmax⟩ := (Finset.Ico n B).exists_max_image f ⟨n,hnB⟩
  have hnk : n ≤ k := (Finset.mem_Ico.mp hk).1
  refine ⟨k,hnk,?_⟩
  intro l hkl
  by_cases hl : l < B
  · exact hmax l (Finset.mem_Ico.mpr ⟨hnk.trans hkl,hl⟩)
  · exact (hN l ((le_max_left N (n+1)).trans (le_of_not_gt hl))).le.trans (hmax n hnB)

theorem exists_tail_records (f : ℕ → ℝ) (hf : ∀ n, 0 < f n)
    (ht : Tendsto f atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ i l, k i ≤ l → f l ≤ f (k i) := by
  choose next hn hnext using exists_tail_maximum f hf ht
  let k : ℕ → ℕ := fun j => Nat.rec (next 0) (fun _ n => next (n+1)) j
  refine ⟨k,strictMono_nat_of_lt_succ (fun i => ?_),?_⟩
  · exact (Nat.lt_succ_self (k i)).trans_le (hn (k i+1))
  · intro i l hl
    cases i with
    | zero => exact hnext 0 l hl
    | succ i => exact hnext (k i+1) l hl

theorem weighted_tail_records (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (b : ℝ) (hb : 0 < b)
    (ht : Tendsto (fun n => A n*b^n) atTop (𝓝 0)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ i j, A (k i+j) ≤ (b^j)⁻¹*A (k i) := by
  obtain ⟨k,hk,htail⟩ := exists_tail_records (fun n => A n*b^n)
    (fun n => mul_pos (hA n) (pow_pos hb n)) ht
  refine ⟨k,hk,?_⟩
  intro i j
  have hh := htail i (k i+j) (Nat.le_add_right _ _)
  rw [pow_add] at hh
  have hdiv : A (k i+j)*b^j ≤ A (k i) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hb (k i))).mp
    nlinarith [hh]
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (pow_pos hb j)).mpr hdiv

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking
open Set Metric Filter Topology

lemma oscillation_le_of_pairwise {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (A : Set X) (hA : IsCompact A)
    (hne : A.Nonempty) (B : ℝ) (hpair : ∀ x ∈ A, ∀ y ∈ A, f x-f y ≤ B) :
    oscillation f A ≤ B := by
  obtain ⟨x,hx,hfx⟩ := (hA.image hf).sSup_mem (hne.image f)
  obtain ⟨y,hy,hfy⟩ := (hA.image hf).sInf_mem (hne.image f)
  simpa only [CannonCrossEnergy.oscillation,← hfx,← hfy] using hpair x hx y hy

theorem connected_oscillation_cover {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    (f : X → ℝ) (hf : Continuous f) (P : Set X) (hP : IsCompact P)
    (hconn : IsConnected P) (A : ι → Set X) (hA : ∀ i, IsCompact (A i))
    (hne : ∀ i, (A i).Nonempty) (hcover : ∀ x ∈ P, ∃ i, x ∈ A i) :
    oscillation f P ≤ ∑ i, oscillation f (A i) := by
  classical
  have hcov : ∀ t ∈ rangeInterval f P,
      (1 : ℝ) ≤ ∑ i, (rangeInterval f (A i)).indicator (fun _ : ℝ => (1 : ℝ)) t := by
    intro t ht
    rw [rangeInterval_eq_image hf hP hconn.1 hconn.2] at ht
    obtain ⟨x,hx,rfl⟩ := ht
    obtain ⟨i,hi⟩ := hcover x hx
    have ht := mem_rangeInterval hf (hA i) hi
    calc
      (1 : ℝ) = (rangeInterval f (A i)).indicator (fun _ : ℝ => (1 : ℝ)) (f x) := by simp [ht]
      _ ≤ _ := Finset.single_le_sum
        (f := fun j : ι => (rangeInterval f (A j)).indicator (fun _ : ℝ => (1 : ℝ)) (f x))
        (fun j _ => Set.indicator_nonneg (by intro; norm_num) _) (Finset.mem_univ i)
  have hh := weighted_interval_cover (fun i => sInf (f '' A i))
    (fun i => sSup (f '' A i)) (fun _ => 1) (sInf (f '' P)) (sSup (f '' P)) 1
    (sub_nonneg.mp (oscillation_nonneg hf hP hconn.1))
    (fun i => sub_nonneg.mp (oscillation_nonneg hf (hA i) (hne i)))
    (fun _ => by norm_num) hcov
  simpa only [one_mul,CannonCrossEnergy.oscillation] using hh

def weightedOscillation {X : Type*} [MetricSpace X]
    (f w : X → ℝ) (O : Set X) (r : ℝ) : ℝ :=
  sSup ((fun x => w x * oscillation f (closedBall x r)) '' O)

lemma weightedOscillation_bounds {X : Type*} [MetricSpace X] [CompactSpace X]
    (f w : X → ℝ) (hf : Continuous f) (O : Set X) (hO : O.Nonempty)
    (hw : ∀ x ∈ O, w x ∈ Icc (0:ℝ) 1) (r : ℝ) (hr : 0 ≤ r)
    (B : ℝ) (_hB : 0 ≤ B) (hbound : ∀ x ∈ O, oscillation f (closedBall x r) ≤ B) :
    0 ≤ weightedOscillation f w O r ∧ weightedOscillation f w O r ≤ B ∧
      ∀ x ∈ O, w x*oscillation f (closedBall x r) ≤ weightedOscillation f w O r := by
  have hpoint (x : X) (hx : x ∈ O) : w x*oscillation f (closedBall x r) ≤ B := by
    have hh := oscillation_nonneg hf (isCompact_closedBall _ _) ⟨x,mem_closedBall_self hr⟩
    calc
      w x*oscillation f (closedBall x r) ≤ 1*B :=
        mul_le_mul (hw x hx).2 (hbound x hx) hh (by norm_num)
      _ = B := one_mul _
  have hBdd : BddAbove ((fun x => w x*oscillation f (closedBall x r)) '' O) :=
    ⟨B,by rintro _ ⟨x,hx,rfl⟩; exact hpoint x hx⟩
  have hne := hO.image (fun x => w x*oscillation f (closedBall x r))
  have hle (x : X) (hx : x ∈ O) : w x*oscillation f (closedBall x r) ≤ weightedOscillation f w O r :=
    le_csSup hBdd (mem_image_of_mem _ hx)
  refine ⟨?_,csSup_le hne (by rintro _ ⟨x,hx,rfl⟩; exact hpoint x hx),hle⟩
  obtain ⟨x,hx⟩ := hO
  exact (mul_nonneg (hw x hx).1
    (oscillation_nonneg hf (isCompact_closedBall _ _) ⟨x,mem_closedBall_self hr⟩)).trans (hle x hx)

theorem weightedOscillation_lower {X : Type*} [MetricSpace X] [CompactSpace X]
    (Q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) Q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f w : X → ℝ) (hf : Continuous f) (O P : Set X)
    (hP : IsCompact P) (hconn : IsConnected P) (hPO : P ⊆ O)
    (hw : ∀ x ∈ O, w x ∈ Icc (0:ℝ) 1)
    (v : ℝ) (_hv : 0 < v) (hvary : v ≤ oscillation f P)
    (η : ℝ) (hη : 0 < η) (hwP : ∀ x ∈ P, η ≤ w x)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x ∈ O, ∀ r, 0 ≤ r → oscillation f (closedBall x r) ≤ B) :
    ∀ r : ℝ, 0 < r → r ≤ 1 →
      (η*v/(max CP 1))*r^Q ≤ weightedOscillation f w O r := by
  classical
  intro r hr hr1
  obtain ⟨T,hTP,hsep,hnet⟩ := CannonNet.exists_finite_separated_net P hP.totallyBounded r hr
  have hO : O.Nonempty := hconn.1.mono hPO
  obtain ⟨hA0,hAB,hA⟩ := weightedOscillation_bounds f w hf O hO hw r hr.le B hB
    (fun x hx => hbound x hx r hr.le)
  have hoc := connected_oscillation_cover f hf P hP hconn
    (fun i : T => closedBall (i : X) r) (fun _ => isCompact_closedBall _ _)
    (fun i => ⟨i.val,mem_closedBall_self hr.le⟩) (fun x hx => by
      obtain ⟨y,hy,hxy⟩ := hnet x hx
      exact ⟨⟨y,hy⟩,mem_closedBall.mpr hxy⟩)
  obtain ⟨p,hp⟩ := hconn.1
  have hcard₀ := hpack p 1 r hr hr1 le_rfl T (fun y _ => hdiam p y) hsep
  have hcard : (Fintype.card T : ℝ) ≤ (max CP 1)*(1/r)^Q := by
    simpa only [Fintype.card_coe] using hcard₀.trans
      (mul_le_mul_of_nonneg_right (le_max_left CP 1) (by positivity))
  have hseed : η*v ≤ (max CP 1)*(1/r)^Q*weightedOscillation f w O r := by
    calc
      η*v ≤ η*oscillation f P := mul_le_mul_of_nonneg_left hvary hη.le
      _ ≤ η*∑ i : T, oscillation f (closedBall (i : X) r) := mul_le_mul_of_nonneg_left hoc hη.le
      _ = ∑ i : T, η*oscillation f (closedBall (i : X) r) := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : T, weightedOscillation f w O r := by
        apply Finset.sum_le_sum
        intro i _
        exact (mul_le_mul_of_nonneg_right (hwP i.val (hTP i.property))
          (oscillation_nonneg hf (isCompact_closedBall _ _) ⟨i.val,mem_closedBall_self hr.le⟩)).trans
            (hA i.val (hPO (hTP i.property)))
      _ = (Fintype.card T : ℝ)*weightedOscillation f w O r := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hA0
  have hpow : 0 < r^Q := pow_pos hr Q
  have hh := mul_le_mul_of_nonneg_right hseed hpow.le
  have heq : (max CP 1)*(1/r)^Q*weightedOscillation f w O r*r^Q =
      (max CP 1)*weightedOscillation f w O r := by
    rw [div_pow,one_pow]
    field_simp
  rw [heq] at hh
  have hCP : 0 < max CP 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hh' : (η*v*r^Q)/(max CP 1) ≤ weightedOscillation f w O r :=
    (div_le_iff₀ hCP).mpr (by nlinarith [hh])
  convert hh' using 1
  ring

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy Set Metric Filter Topology

lemma infDist_compl_weight {X : Type*} [MetricSpace X]
    (O : Set X) (hO : IsOpen O) (hne : Oᶜ.Nonempty)
    (hdiam : ∀ x y : X, dist x y ≤ 1) (q : ℕ) :
    ∀ x ∈ O, 0 < infDist x Oᶜ ^ (q+1) ∧ infDist x Oᶜ ^ (q+1) ≤ 1 := by
  intro x hx
  have hd : 0 < infDist x Oᶜ := (hO.isClosed_compl.notMem_iff_infDist_pos hne).mp (by simpa)
  have hd1 : infDist x Oᶜ ≤ 1 := by
    obtain ⟨y,hy⟩ := hne
    exact (infDist_le_dist_of_mem hy).trans (hdiam x y)
  exact ⟨pow_pos hd _,pow_le_one₀ hd.le hd1⟩

lemma infDist_compl_compact_lower {X : Type*} [MetricSpace X]
    (O P : Set X) (hO : IsOpen O) (hne : Oᶜ.Nonempty)
    (hP : IsCompact P) (hPe : P.Nonempty) (hPO : P ⊆ O) (q : ℕ) :
    ∃ η > 0, ∀ x ∈ P, η ≤ infDist x Oᶜ ^ (q+1) := by
  obtain ⟨x,hx,hmin⟩ := hP.exists_isMinOn hPe ((continuous_infDist_pt Oᶜ).pow (q+1)).continuousOn
  refine ⟨_,pow_pos ((hO.isClosed_compl.notMem_iff_infDist_pos hne).mp (by simpa using hPO hx)) _,hmin⟩

theorem weighted_centers_escape (q : ℕ) (r δ A : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hδ : ∀ i, 0 ≤ δ i)
    (hrt : Tendsto r atTop (𝓝 0)) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B)
    (hlower : ∀ i, c*(r i)^q ≤ A i)
    (hselected : ∀ i, A i ≤ 2*(δ i)^(q+1)*B) :
    Tendsto (fun i => δ i/r i) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro L
  let T : ℝ := max L 1
  have hT : 0 < T := zero_lt_one.trans_le (le_max_right _ _)
  have ht : Tendsto (fun i => 2*B*T^(q+1)*r i) atTop (𝓝 0) := by
    simpa only [mul_zero] using hrt.const_mul (2*B*T^(q+1))
  filter_upwards [ht.eventually (gt_mem_nhds hc)] with i hi
  have hlarge : T < δ i/r i := by
    by_contra hn
    have hδT : δ i ≤ T*r i := (div_le_iff₀ (hr i)).mp (le_of_not_gt hn)
    have hp := pow_le_pow_left₀ (hδ i) hδT (q+1)
    have hh : c*(r i)^q ≤ (2*B*T^(q+1)*r i)*(r i)^q := by
      calc
        c*(r i)^q ≤ A i := hlower i
        _ ≤ 2*(δ i)^(q+1)*B := hselected i
        _ ≤ 2*(T*r i)^(q+1)*B := by nlinarith [hp]
        _ = _ := by rw [mul_pow,pow_succ (r i)]; ring
    have hh' := (mul_le_mul_iff_left₀ (pow_pos (hr i) q)).mp hh
    exact (not_le_of_gt hi) hh'
  exact (le_max_left L 1).trans hlarge.le

theorem select_weighted_magnifications {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X → ℝ) (hf : Continuous f) (O : Set X) (hO : IsOpen O)
    (hOe : O.Nonempty) (hOc : Oᶜ.Nonempty)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (q : ℕ) (a : ℝ) (ha : 1 < a) (β b : ℝ)
    (hβ : 0 < β) (hb : 1 < b) (hβb : β*b < 1)
    (c C B : ℝ) (hc : 0 < c) (_hC : 0 ≤ C) (hB : 0 ≤ B)
    (hbound : ∀ x ∈ O, ∀ r, 0 ≤ r → oscillation f (closedBall x r) ≤ B)
    (hlower : ∀ n : ℕ, c*((a^n)⁻¹)^q ≤
      weightedOscillation f (fun x => infDist x Oᶜ ^ (q+1)) O ((a^n)⁻¹))
    (hupper : ∀ n : ℕ,
      weightedOscillation f (fun x => infDist x Oᶜ ^ (q+1)) O ((a^n)⁻¹) ≤ C*β^n) :
    ∃ (k : ℕ → ℕ) (x : ℕ → X) (σ : ℕ → ℝ), StrictMono k ∧
      (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      (∀ i, σ i/2 < oscillation f (closedBall (x i) ((a^(k i))⁻¹))) ∧
      (∀ i j y, y ∈ O →
        infDist y Oᶜ ^ (q+1) * oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤
          (b^j)⁻¹ * σ i * infDist (x i) Oᶜ ^ (q+1)) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop := by
  classical
  let w : X → ℝ := fun x => infDist x Oᶜ ^ (q+1)
  let A : ℕ → ℝ := fun n => weightedOscillation f w O ((a^n)⁻¹)
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hr (n : ℕ) : 0 < (a^n)⁻¹ := inv_pos.mpr (pow_pos ha0 n)
  have hw (x : X) (hx : x ∈ O) : 0 < w x ∧ w x ≤ 1 := infDist_compl_weight O hO hOc hdiam q x hx
  have hAbounds (n : ℕ) := weightedOscillation_bounds f w hf O hOe
    (fun x hx => ⟨(hw x hx).1.le,(hw x hx).2⟩) _ (hr n).le B hB
      (fun x hx => hbound x hx _ (hr n).le)
  have hApos (n : ℕ) : 0 < A n := (mul_pos hc (pow_pos (hr n) q)).trans_le (hlower n)
  have ht : Tendsto (fun n => A n*b^n) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_pos hβ (zero_lt_one.trans hb)).le hβb
    have ht' : Tendsto (fun n : ℕ => C*(β*b)^n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hp.const_mul C
    apply squeeze_zero (fun n => (mul_pos (hApos n) (pow_pos (zero_lt_one.trans hb) n)).le) _ ht'
    intro n
    simpa only [mul_pow,mul_assoc] using mul_le_mul_of_nonneg_right (hupper n)
      (pow_nonneg (zero_lt_one.trans hb).le n)
  obtain ⟨k,hk,htail⟩ := weighted_tail_records A hApos b (zero_lt_one.trans hb) ht
  have hchoose (i : ℕ) : ∃ x ∈ O, A (k i)/2 < w x*oscillation f (closedBall x ((a^(k i))⁻¹)) := by
    obtain ⟨v,⟨x,hx,hv⟩,hval⟩ := exists_lt_of_lt_csSup
      (s := (fun x => w x*oscillation f (closedBall x ((a^(k i))⁻¹))) '' O)
      (hOe.image _) (show A (k i)/2 < A (k i) by linarith [hApos (k i)])
    exact ⟨x,hx,by simpa only [← hv] using hval⟩
  choose x hx hsel using hchoose
  let σ : ℕ → ℝ := fun i => A (k i)/w (x i)
  have hσ (i : ℕ) : 0 < σ i := div_pos (hApos _) (hw _ (hx i)).1
  have hσeq (i : ℕ) : σ i*w (x i) = A (k i) := div_mul_cancel₀ _ (ne_of_gt (hw _ (hx i)).1)
  refine ⟨k,x,σ,hk,(fun i => ⟨hx i,hσ i⟩),?_,?_,?_⟩
  · intro i
    apply (div_lt_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (div_lt_iff₀ (hw _ (hx i)).1).mpr
    nlinarith [hsel i]
  · intro i j y hy
    have hh := (hAbounds (k i+j)).2.2 y hy
    have hh' := hh.trans (htail i j)
    change w y*oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤ (b^j)⁻¹*σ i*w (x i)
    simpa only [mul_assoc,hσeq i] using hh'
  · refine weighted_centers_escape q (fun i => (a^(k i))⁻¹) (fun i => infDist (x i) Oᶜ)
      (fun i => A (k i)) (fun i => hr (k i)) (fun _ => infDist_nonneg)
      ?_ c B hc hB (fun i => hlower (k i)) ?_
    · simpa only [inv_pow,Function.comp_def] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr ha0).le (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
    · intro i
      have hh := hbound (x i) (hx i) _ (hr (k i)).le
      have hh' := mul_le_mul_of_nonneg_left hh (hw _ (hx i)).1.le
      change A (k i) ≤ 2*w (x i)*B
      nlinarith [hsel i,hh']

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

lemma inverse_geometric_near {a s : ℝ} (ha : 1 < a) (l₀ : ℕ) (hs : 0 < s)
    (hsmall : s ≤ (a^l₀)⁻¹) :
    ∃ l : ℕ, l₀ ≤ l ∧ s ≤ (a^l)⁻¹ ∧ (a^l)⁻¹ < a*s := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hsone : s ≤ 1 := hsmall.trans (inv_le_one_of_one_le₀ (one_le_pow₀ ha.le))
  obtain ⟨l,hl₁,hl₂⟩ := exists_nat_pow_near_of_lt_one hs hsone
    (inv_pos.mpr hap) (inv_lt_one_of_one_lt₀ ha)
  have hl₀ : l₀ ≤ l := by
    by_contra hn
    have hle : l+1 ≤ l₀ := by omega
    have hh := pow_le_pow_of_le_one (inv_nonneg.mpr hap.le)
      (inv_lt_one_of_one_lt₀ ha).le hle
    rw [inv_pow,inv_pow] at hh
    rw [inv_pow] at hl₁
    exact (hl₁.trans_le (hsmall.trans hh)).false
  refine ⟨l,hl₀,by simpa only [inv_pow] using hl₂,?_⟩
  have hh := mul_lt_mul_of_pos_right hl₁ hap
  rw [pow_succ,inv_pow] at hh
  simpa only [mul_assoc,inv_mul_cancel₀ hap.ne',mul_one,mul_comm s a] using hh

lemma reciprocal_pow_log {a lam : ℝ} (ha : 1 < a) (hlam : 0 < lam) (l : ℕ) :
    ((a^l)⁻¹) ^ (Real.log lam / Real.log a) = (lam^l)⁻¹ := by
  have hap : 0 < a := zero_lt_one.trans ha
  have hlog : Real.log a ≠ 0 := (Real.log_pos ha).ne'
  apply Real.log_injOn_pos (Real.rpow_pos_of_pos (inv_pos.mpr (pow_pos hap l)) _)
    (inv_pos.mpr (pow_pos hlam l))
  rw [Real.log_rpow (inv_pos.mpr (pow_pos hap l)),Real.log_inv,Real.log_inv,
    Real.log_pow,Real.log_pow]
  field_simp

lemma abs_sub_le_oscillation {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (A : Set X) (hA : IsCompact A)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) : |f x-f y| ≤ oscillation f A := by
  have hx' := mem_rangeInterval hf hA hx
  have hy' := mem_rangeInterval hf hA hy
  change sInf (f '' A) ≤ f x ∧ f x ≤ sSup (f '' A) at hx'
  change sInf (f '' A) ≤ f y ∧ f y ≤ sSup (f '' A) at hy'
  change |f x-f y| ≤ sSup (f '' A)-sInf (f '' A)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma infDist_comparable {X : Type*} [MetricSpace X]
    (O : Set X) {x y : X} (hx : 0 < infDist x Oᶜ)
    (hxy : dist x y ≤ infDist x Oᶜ/2) :
    y ∈ O ∧ infDist x Oᶜ ≤ 2*infDist y Oᶜ := by
  have hy := notMem_of_dist_lt_infDist (s := Oᶜ) (lt_of_le_of_lt hxy (by linarith))
  have hh := infDist_le_infDist_add_dist (x := x) (y := y) (s := Oᶜ)
  exact ⟨by simpa using hy,by linarith⟩

theorem normalized_local_oscillation {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X → ℝ) (_hf : Continuous f) (O : Set X) (q : ℕ)
    (x y : X) (r σ t : ℝ) (_hr : 0 ≤ r) (hσ : 0 < σ) (ht : 0 ≤ t)
    (hx : 0 < infDist x Oᶜ) (hxy : dist x y ≤ infDist x Oᶜ/2)
    (hrec : ∀ y ∈ O, infDist y Oᶜ^(q+1)*oscillation f (closedBall y r) ≤
      t*σ*infDist x Oᶜ^(q+1)) :
    oscillation f (closedBall y r)/σ ≤ 2^(q+1)*t := by
  obtain ⟨hy,hδ⟩ := infDist_comparable O hx hxy
  have hδy : 0 < infDist y Oᶜ := by linarith
  have hp := pow_le_pow_left₀ infDist_nonneg hδ (q+1)
  rw [mul_pow] at hp
  have hc := (hrec y hy).trans (mul_le_mul_of_nonneg_left hp (mul_nonneg ht hσ.le))
  apply (div_le_iff₀ hσ).mpr
  have hh : infDist y Oᶜ^(q+1)*oscillation f (closedBall y r) ≤
      infDist y Oᶜ^(q+1)*(2^(q+1)*t*σ) := hc.trans_eq (by ring)
  exact (mul_le_mul_iff_right₀ (pow_pos hδy (q+1))).mp hh

theorem bounded_connected_variation {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) q CP)
    (f : X → ℝ) (hf : Continuous f) (P : Set X) (hP : IsCompact P)
    (hconn : IsConnected P) (x : X) (r D σ A : ℝ)
    (hr : 0 < r) (hD : 1 ≤ D) (hDr : D*r ≤ 1) (hσ : 0 < σ) (hA : 0 ≤ A)
    (hball : ∀ y ∈ P, dist x y ≤ D*r)
    (hlocal : ∀ y ∈ P, oscillation f (closedBall y r)/σ ≤ A) :
    oscillation f P/σ ≤ CP*D^q*A := by
  classical
  obtain ⟨T,hTP,hsep,hnet⟩ := CannonNet.exists_finite_separated_net P hP.totallyBounded r hr
  have hoc := connected_oscillation_cover f hf P hP hconn
    (fun i : T => closedBall (i : X) r) (fun _ => isCompact_closedBall _ _)
    (fun i => ⟨i.val,mem_closedBall_self hr.le⟩) (fun y hy => by
      obtain ⟨z,hz,hyz⟩ := hnet y hy
      exact ⟨⟨z,hz⟩,mem_closedBall.mpr hyz⟩)
  have hcard : (Fintype.card T : ℝ) ≤ CP*D^q := by
    have hh := hpack x (D*r) r hr (by nlinarith) hDr T
      (fun y hy => hball y (hTP hy)) hsep
    simpa only [Fintype.card_coe,mul_div_cancel_right₀ D hr.ne'] using hh
  calc
    oscillation f P/σ ≤ (∑ i : T, oscillation f (closedBall (i : X) r))/σ :=
      div_le_div_of_nonneg_right hoc hσ.le
    _ = ∑ i : T, oscillation f (closedBall (i : X) r)/σ := Finset.sum_div _ _ _
    _ ≤ ∑ _i : T, A := Finset.sum_le_sum (fun i _ => hlocal i.val (hTP i.property))
    _ = (Fintype.card T : ℝ)*A := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hA

theorem holder_of_geometric_bounds (a b D C t V : ℝ)
    (ha : 1 < a) (hb : 1 < b) (hD : 0 < D) (hC : 0 ≤ C) (ht : 0 < t)
    (hsmall : D*t ≤ 1)
    (hdiscrete : ∀ j : ℕ, D*t ≤ (a^j)⁻¹ → V ≤ C*(b^j)⁻¹) :
    V ≤ (C*(a*D)^(Real.log b/Real.log a))*t^(Real.log b/Real.log a) := by
  have hα : 0 < Real.log b/Real.log a := div_pos (Real.log_pos hb) (Real.log_pos ha)
  obtain ⟨j,_hj,hj₁,hj₂⟩ := inverse_geometric_near ha 0 (mul_pos hD ht) (by simpa using hsmall)
  have hh := hdiscrete j hj₁
  rw [← reciprocal_pow_log ha (zero_lt_one.trans hb) j] at hh
  apply hh.trans
  have hp := Real.rpow_le_rpow
    (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans ha).le j)) hj₂.le hα.le
  apply (mul_le_mul_of_nonneg_left hp hC).trans_eq
  rw [show a*(D*t) = (a*D)*t by ring,Real.mul_rpow (by positivity) ht.le]
  ring

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

def normalized {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (h : X ≃ₜ X) (x : X) (σ : ℝ) (z : X) : ℝ := (f (h.symm z)-f x)/σ

lemma continuous_normalized {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (hf : Continuous f) (h : X ≃ₜ X) (x : X) (σ : ℝ) : Continuous (normalized f h x σ) :=
  ((hf.comp h.symm.continuous).sub continuous_const).div_const σ

lemma normalized_dist {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (h : X ≃ₜ X) (x : X) (σ : ℝ) (hσ : 0 < σ) (z w : X) :
    dist (normalized f h x σ z) (normalized f h x σ w) =
      |f (h.symm z)-f (h.symm w)|/σ := by
  have hh : normalized f h x σ z-normalized f h x σ w =
      (f (h.symm z)-f (h.symm w))/σ := by unfold normalized; ring
  rw [Real.dist_eq,hh,abs_div,abs_of_pos hσ]

lemma compact_puncture_separation {X : Type*} [MetricSpace X]
    (K : Set X) (hK : IsCompact K) (p : ℕ → X) (b : X) (hb : b ∉ K)
    (hp : Tendsto p atTop (𝓝 b)) :
    ∃ e > 0, ∀ᶠ n in atTop, ∀ z ∈ K, e ≤ dist z (p n) := by
  rcases K.eq_empty_or_nonempty with hKe | hKe
  · exact ⟨1,zero_lt_one,Eventually.of_forall (by simp [hKe])⟩
  have hd : 0 < infDist b K := (hK.isClosed.notMem_iff_infDist_pos hKe).mp hb
  refine ⟨infDist b K/2,by positivity,?_⟩
  filter_upwards [hp.eventually (ball_mem_nhds b (half_pos hd))] with n hn z hz
  have hz' := infDist_le_dist_of_mem (x := b) hz
  have ht := dist_triangle b (p n) z
  rw [dist_comm b z] at hz'
  rw [dist_comm b (p n),dist_comm (p n) z,dist_comm b z] at ht
  have hn' := mem_ball.mp hn
  linarith

theorem normalized_bounds_at_scale {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) q CP)
    (f : X → ℝ) (hf : Continuous f) (O : Set X)
    (L B D r a b σ : ℝ) (hL : 1 ≤ L) (hB : 1 ≤ B) (_hD : 0 < D)
    (hr : 0 < r) (ha : 1 < a) (hb : 1 < b) (hσ : 0 < σ)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < L*s} u v)
    (h : X ≃ₜ X) (x : X) (K : Set X)
    (hx : 0 < infDist x Oᶜ) (hdeep : 2*(L*B)*r ≤ infDist x Oᶜ)
    (hsmall : (L*B)*r ≤ 1)
    (hpre : ∀ z ∈ K, dist x (h.symm z) ≤ B*r)
    (hlip : ∀ z ∈ K, ∀ w ∈ K, dist (h.symm z) (h.symm w) ≤ D*r*dist z w)
    (hrec : ∀ j : ℕ, ∀ y ∈ O,
      infDist y Oᶜ^(q+1)*oscillation f (closedBall y (r*(a^j)⁻¹)) ≤
        (b^j)⁻¹*σ*infDist x Oᶜ^(q+1)) :
    (∀ z ∈ K, |normalized f h x σ z| ≤ CP*(L*B)^q*2^(q+1)) ∧
    (∀ z ∈ K, ∀ w ∈ K, ∀ j : ℕ, D*dist z w ≤ (a^j)⁻¹ →
      dist (normalized f h x σ z) (normalized f h x σ w) ≤ 2^(q+1)*(b^j)⁻¹) := by
  have hR : 1 ≤ L*B := one_le_mul_of_one_le_of_one_le hL hB
  have hBr : 0 < B*r := mul_pos (zero_lt_one.trans_le hB) hr
  have hBR : B*r ≤ (L*B)*r := by nlinarith
  have hcenter (y : X) (hy : dist x y ≤ (L*B)*r) : dist x y ≤ infDist x Oᶜ/2 := by linarith
  have hlocal (j : ℕ) (y : X) (hy : dist x y ≤ (L*B)*r) :
      oscillation f (closedBall y (r*(a^j)⁻¹))/σ ≤ 2^(q+1)*(b^j)⁻¹ :=
    normalized_local_oscillation f hf O q x y _ σ _
      (mul_nonneg hr.le (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans ha).le j))) hσ
      (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans hb).le j)) hx (hcenter y hy) (hrec j)
  constructor
  · intro z hz
    obtain ⟨γ,hγ⟩ := hpaths x x (h.symm z) (B*r) hBr (by simp; exact hBr.le) (hpre z hz)
    have hP : IsCompact (range γ) := isCompact_range γ.continuous
    have hconn : IsConnected (range γ) := isConnected_range γ.continuous
    have hh := bounded_connected_variation q CP hpack f hf (range γ) hP hconn x r (L*B) σ (2^(q+1))
      hr hR hsmall hσ (by positivity) (by
        rintro y ⟨t,rfl⟩
        exact (hγ t).le.trans_eq (by ring)) (by
        rintro y ⟨t,rfl⟩
        simpa only [pow_zero,inv_one,mul_one] using hlocal 0 (γ t) ((hγ t).le.trans_eq (by ring)))
    have hvar := abs_sub_le_oscillation f hf (range γ) hP
      (show h.symm z ∈ range γ from ⟨1,γ.target⟩) (show x ∈ range γ from ⟨0,γ.source⟩)
    unfold normalized
    rw [abs_div,abs_of_pos hσ]
    exact (div_le_div_of_nonneg_right hvar hσ.le).trans hh
  · intro z hz w hw j hj
    have hd : dist (h.symm w) (h.symm z) ≤ r*(a^j)⁻¹ := by
      rw [dist_comm]
      calc
        dist (h.symm z) (h.symm w) ≤ D*r*dist z w := hlip z hz w hw
        _ ≤ r*(a^j)⁻¹ := by nlinarith [mul_le_mul_of_nonneg_left hj hr.le]
    have hc := hlocal j (h.symm z) ((hpre z hz).trans hBR)
    have hvar := abs_sub_le_oscillation f hf (closedBall (h.symm z) (r*(a^j)⁻¹))
      (isCompact_closedBall _ _) (mem_closedBall_self (by positivity)) (mem_closedBall.mpr hd)
    rw [normalized_dist f h x σ hσ]
    exact (div_le_div_of_nonneg_right hvar hσ.le).trans hc

theorem global_holder_of_discrete {X : Type*} [MetricSpace X]
    (F : X → ℝ) (K : Set X) (a b D M C : ℝ)
    (ha : 1 < a) (hb : 1 < b) (hD : 0 < D) (_hM : 0 ≤ M) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ K, |F z| ≤ M)
    (hdiscrete : ∀ z ∈ K, ∀ w ∈ K, ∀ j : ℕ, D*dist z w ≤ (a^j)⁻¹ →
      dist (F z) (F w) ≤ C*(b^j)⁻¹) :
    ∀ z ∈ K, ∀ w ∈ K,
      dist (F z) (F w) ≤
        max (C*(a*D)^(Real.log b/Real.log a)) (2*M*D^(Real.log b/Real.log a)) *
          (dist z w)^(Real.log b/Real.log a) := by
  intro z hz w hw
  let α := Real.log b/Real.log a
  have hα : 0 < α := div_pos (Real.log_pos hb) (Real.log_pos ha)
  by_cases heq : z = w
  · subst w
    have hαne : Real.log b/Real.log a ≠ 0 := hα.ne'
    simp only [dist_self,Real.zero_rpow hαne,mul_zero,le_refl]
  have ht : 0 < dist z w := dist_pos.mpr heq
  by_cases hsmall : D*dist z w ≤ 1
  · exact (holder_of_geometric_bounds a b D C (dist z w) (dist (F z) (F w))
      ha hb hD hC ht hsmall (hdiscrete z hz w hw)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  · have hp : 1 ≤ D^α*(dist z w)^α := by
      rw [← Real.mul_rpow hD.le ht.le]
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ)≤1)
        (le_of_not_ge hsmall) hα.le
    have hdist : dist (F z) (F w) ≤ 2*M := by
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hbound z hz,hbound w hw])
    calc
      dist (F z) (F w) ≤ 2*M := hdist
      _ ≤ (2*M*D^α)*(dist z w)^α := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

theorem expansion_record_tails {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f : X → ℝ) (hf : Continuous f) (O : Set X) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (Lp a b CE LE d : ℝ) (hLp : 1 ≤ Lp) (ha : 1 < a) (hb : 1 < b)
    (hCE : 0 ≤ CE) (hLE : 0 < LE) (hd : 0 < d)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < Lp*s} u v)
    (k : ℕ → ℕ) (hk : StrictMono k) (x : ℕ → X) (σ : ℕ → ℝ)
    (hx : ∀ i, x i ∈ O) (hσ : ∀ i, 0 < σ i)
    (h : ℕ → X ≃ₜ X) (z₀ pLim : X)
    (hsep : ∀ i, d ≤ dist (x i) z₀)
    (hexp : ∀ i, Expansion (h i) (x i) ((a^(k i))⁻¹) CE LE)
    (hp : Tendsto (fun i => h i z₀) atTop (𝓝 pLim))
    (hescape : Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop)
    (hrec : ∀ i j y, y ∈ O →
      infDist y Oᶜ ^ (q+1) * oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤
        (b^j)⁻¹ * σ i * infDist (x i) Oᶜ ^ (q+1)) :
    ∀ K : Set X, IsCompact K → pLim ∉ K → ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧
      ∀ᶠ i in atTop,
        (∀ z ∈ K, (h i).symm z ∈ O) ∧
        (∀ z ∈ K, |normalized f (h i) (x i) (σ i) z| ≤ M) ∧
        (∀ z ∈ K, ∀ w ∈ K,
          dist (normalized f (h i) (x i) (σ i) z) (normalized f (h i) (x i) (σ i) w) ≤
            H*(dist z w)^(Real.log b/Real.log a)) := by
  intro K hK hKp
  obtain ⟨e,he,hep⟩ := compact_puncture_separation K hK (fun i => h i z₀) pLim hKp hp
  let B := max 1 (CE/(e*d))
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  let R := Lp*B
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le hLp hB
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hBR : B ≤ R := by dsimp [R]; nlinarith
  let D := LE*B^2
  have hD : 0 < D := mul_pos hLE (pow_pos hB0 2)
  let M := CP*R^q*2^(q+1)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let H := max (2^(q+1)*(a*D)^(Real.log b/Real.log a))
    (2*M*D^(Real.log b/Real.log a))
  have hH : 0 ≤ H := (show 0 ≤ 2^(q+1)*(a*D)^(Real.log b/Real.log a) by positivity).trans
    (le_max_left _ _)
  have hr (i : ℕ) : 0 < (a^(k i))⁻¹ := inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _)
  have hrt : Tendsto (fun i => (a^(k i))⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
  have hsmall : ∀ᶠ i in atTop, R*(a^(k i))⁻¹ ≤ 1 := by
    have ht : Tendsto (fun i => R*(a^(k i))⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using hrt.const_mul R
    exact (ht.eventually (gt_mem_nhds zero_lt_one)).mono (fun _ hn => hn.le)
  refine ⟨M,H,hM,hH,?_⟩
  filter_upwards [hep,hsmall,hescape.eventually (eventually_ge_atTop (2*R))] with i hi hsmall hdeep
  have hδx : 0 < infDist (x i) Oᶜ :=
    (hO.isClosed_compl.notMem_iff_infDist_pos hOc).mp (by simpa using hx i)
  have hdeep' : 2*R*(a^(k i))⁻¹ ≤ infDist (x i) Oᶜ := (le_div_iff₀ (hr i)).mp hdeep
  have hpre (z : X) (hz : z ∈ K) : dist (x i) ((h i).symm z) ≤ B*(a^(k i))⁻¹ := by
    exact (preimage_distance_bound (h i) (x i) z₀ z _ CE LE e d (hr i) hCE he hd
      (hexp i) hdiam (hsep i) (hi z hz)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (hr i).le)
  have hlip (z : X) (hz : z ∈ K) (w : X) (hw : w ∈ K) :
      dist ((h i).symm z) ((h i).symm w) ≤ D*(a^(k i))⁻¹*dist z w := by
    have hh := inverse_lipschitz_on_preimages (h i) (x i) z w _ CE LE B (hr i) hLE.le
      (hexp i) (hpre z hz) (hpre w hw)
    simpa only [max_eq_right hB] using hh
  have hrec' (j : ℕ) (y : X) (hy : y ∈ O) :
      infDist y Oᶜ^(q+1)*oscillation f (closedBall y ((a^(k i))⁻¹*(a^j)⁻¹)) ≤
        (b^j)⁻¹*σ i*infDist (x i) Oᶜ^(q+1) := by
    simpa only [pow_add,mul_inv_rev,mul_comm] using hrec i j y hy
  obtain ⟨hbound,hdiscrete⟩ := normalized_bounds_at_scale q CP hpack f hf O
    Lp B D ((a^(k i))⁻¹) a b (σ i) hLp hB hD (hr i) ha hb (hσ i)
    hpaths (h i) (x i) K hδx hdeep' hsmall hpre hlip hrec'
  refine ⟨fun z hz => ?_,hbound,?_⟩
  · exact (infDist_comparable O hδx (by
      have hh := hpre z hz
      have hh' := mul_le_mul_of_nonneg_right hBR (hr i).le
      linarith)).1
  · exact global_holder_of_discrete (normalized f (h i) (x i) (σ i)) K
      a b D M (2^(q+1)) ha hb hD hM (by positivity) hbound hdiscrete

end CannonMagnification

open Set Filter Topology Metric

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
