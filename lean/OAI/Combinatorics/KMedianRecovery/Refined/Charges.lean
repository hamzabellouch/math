import OAI.Combinatorics.KMedianRecovery.Recovery.Ball
import OAI.Combinatorics.KMedianRecovery.Recovery.NearMass
import OAI.Combinatorics.KMedianRecovery.Recovery.Destination

namespace OAI

/-! Near-client mass, population radii, and the five classes of cluster charge. -/

namespace MetricKMedianRecovery.RefinedRecovery.Analysis

noncomputable def q (μ : ℝ) := μ / (1 + μ)

lemma q_pos {μ : ℝ} (hμ : 0 < μ) : 0 < q μ :=
  div_pos hμ (by linarith)

lemma q_eq {μ : ℝ} (hμ : 0 < μ) : q μ = 1 - 1/(1+μ) := by
  unfold q
  field_simp
  ring

lemma near_bound {V : Type*} [PseudoMetricSpace V] [DecidableEq V]
    (C : Finset V) (hC : C.Nonempty) (o : V) (mean μ : ℝ) (hμ : 0 < μ)
    (H : V → ℝ) (hmean : ∑ p ∈ C, dist p o = mean * C.card)
    (hH : ∀ p ∈ C, 0 ≤ H p) (htri : ∀ p ∈ C, H o ≤ dist p o + H p) :
    H o ≤ (1+μ)*mean +
      NearClients.nearMass C o mean (1+μ) H / (q μ * C.card) := by
  rw [q_eq hμ]
  exact NearClients.center_bound C hC o mean (1+μ) (1+μ) H hmean (by linarith) le_rfl hH htri

lemma radius_sum {V K : Type*} [PseudoMetricSpace V] [DecidableEq V]
    (D : Finset V) (hD : D.Nonempty) (A : Finset K) (cluster : K → Finset V)
    (center leader : K → V) (mean : K → ℝ) (P : ℝ) (m : ℕ)
    (hP : 0 < P) (hm : 0 < m) (hA : A.card ≤ m)
    (hc : ∀ i ∈ A, (cluster i).Nonempty) (hcD : ∀ i ∈ A, cluster i ⊆ D)
    (hmean : ∀ i ∈ A, ∑ p ∈ cluster i, dist p (center i) = mean i * (cluster i).card)
    (hcost : (∑ i ∈ A, mean i * (cluster i).card) ≤ P)
    (hnear : ∀ i ∈ A, dist (leader i) (center i) ≤ (3/2 : ℝ) * mean i) :
    (∑ i ∈ A, (cluster i).card * Population.radius D hD P m (leader i)) ≤ (11/2 : ℝ)*P := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hcR : ∀ i ∈ A, (0 : ℝ) < (cluster i).card :=
    fun i hi => Nat.cast_pos.mpr (hc i hi).card_pos
  have hpoint : ∀ i ∈ A,
      (cluster i).card * Population.radius D hD P m (leader i) ≤
        (7/2 : ℝ)*(mean i * (cluster i).card) + 2*P/m := by
    intro i hi
    have hh := Population.leader_radius_le D (cluster i) hD (hc i hi) (hcD i hi)
      P m (leader i) (center i) (mean i) (3/2) hP hm (by norm_num) (hmean i hi) (hnear i hi)
    have hh' := mul_le_mul_of_nonneg_left hh (hcR i hi).le
    apply hh'.trans_eq
    field_simp [ne_of_gt (hcR i hi), ne_of_gt hmR]
    ring
  calc
    _ ≤ ∑ i ∈ A, ((7/2 : ℝ)*(mean i * (cluster i).card) + 2*P/m) :=
      Finset.sum_le_sum hpoint
    _ = (7/2 : ℝ)*(∑ i ∈ A, mean i * (cluster i).card) + A.card * (2*P/m) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (7/2 : ℝ)*P + m*(2*P/m) := by
      apply add_le_add (mul_le_mul_of_nonneg_left hcost (by norm_num))
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hA
    _ = (11/2 : ℝ)*P := by field_simp; ring

noncomputable def baseCharge {E : Type*} (θ H : ℝ) (d : E → ℝ) (X : Finset E) : ℝ :=
  θ*H + (1-θ)*Completion.cappedCost H d X

lemma baseCharge_le_base {E : Type*} {θ : ℝ} (hθ : θ ≤ 1)
    (H : ℝ) (d : E → ℝ) (X : Finset E) : baseCharge θ H d X ≤ H := by
  have hh := mul_le_mul_of_nonneg_left (Completion.cappedCost_le_base H d X)
    (show 0 ≤ 1-θ by linarith)
  dsimp only [baseCharge]
  nlinarith

lemma baseCharge_le_offer {E : Type*} {θ : ℝ} (hθ : θ ≤ 1)
    (H : ℝ) (d : E → ℝ) (X : Finset E) (e : E) (he : e ∈ X) :
    baseCharge θ H d X ≤ θ*H + (1-θ)*d e := by
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Completion.cappedCost_le_offer H d he)
    (show 0 ≤ 1-θ by linarith))

lemma baseCharge_le_center {E : Type*} {θ : ℝ} (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1)
    (H : ℝ) (d : E → ℝ) (X : Finset E) (e : E) (he : e ∈ X) (b : ℝ)
    (hH : H ≤ d e + b) : baseCharge θ H d X ≤ d e + θ*b := by
  apply (baseCharge_le_offer ht1 H d X e he).trans
  have h := mul_le_mul_of_nonneg_left hH ht0
  nlinarith

variable {V : Type*} [DecidableEq V]

noncomputable def clusterCharge (C J : Finset V) (c b : V → ℝ) : ℝ :=
  ∑ p ∈ C, if p ∈ J then c p else b p

lemma clusterCharge_le (C J : Finset V) (c b f : V → ℝ)
    (hc : ∀ p ∈ C, p ∈ J → c p ≤ f p) (hb : ∀ p ∈ C, p ∉ J → b p ≤ f p) :
    clusterCharge C J c b ≤ ∑ p ∈ C, f p := by
  apply Finset.sum_le_sum
  intro p hp
  split_ifs with h
  · exact hc p hp h
  · exact hb p hp h

lemma clusterCharge_eq (C J : Finset V) (c b : V → ℝ) :
    clusterCharge C J c b = (∑ p ∈ C ∩ J, c p) + ∑ p ∈ C \ J, b p := by
  simp only [clusterCharge, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff]

lemma good_charge {E : Type*} (C J : Finset V) (θ : ℝ) (hθ : θ ≤ 1)
    (H proxy : V → ℝ) (d : V → E → ℝ) (X : Finset E)
    (hproxy : ∀ p ∈ C, H p ≤ proxy p) :
    clusterCharge C J proxy (fun p => baseCharge θ (H p) (d p) X) ≤ ∑ p ∈ C, proxy p := by
  apply clusterCharge_le
  · exact fun _ _ _ => le_rfl
  · exact fun p hp _ => (baseCharge_le_base hθ (H p) (d p) X).trans (hproxy p hp)

lemma first_covered {E : Type*} (C J : Finset V) (H d₀ : V → ℝ)
    (offers : V → E → ℝ) (X : Finset E) (e : E) (he : e ∈ X)
    (θ κ a mean r R r₀ P : ℝ) (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1) (hκ : 0 ≤ κ)
    (hown : ∀ p ∈ C, offers p e = d₀ p) (hH : ∀ p ∈ C, H p ≤ d₀ p + r + R)
    (hmean : mean * C.card = P) (hP : ∑ p ∈ C, d₀ p = P)
    (hr : r ≤ a*mean) (hR : R ≤ (1+κ)*r + κ*r₀) :
    clusterCharge C J (fun p => d₀ p + θ*(r+R))
      (fun p => baseCharge θ (H p) (offers p) X) ≤
      (1+2*θ*a)*P + θ*κ*a*P + θ*κ*C.card*r₀ := by
  have hh : clusterCharge C J (fun p => d₀ p + θ*(r+R))
      (fun p => baseCharge θ (H p) (offers p) X) ≤ P + C.card * (θ*(r+R)) := by
    have h := clusterCharge_le C J _ _ (fun p => d₀ p + θ*(r+R))
      (fun _ _ _ => le_rfl) (fun p hp _ => by
        have hh := baseCharge_le_center ht0 ht1 (H p) (offers p) X e he (r+R)
          (by rw [hown p hp]; linarith [hH p hp])
        simpa only [hown p hp] using hh)
    simpa only [Finset.sum_add_distrib, hP, Finset.sum_const, nsmul_eq_mul] using h
  have hrR : r+R ≤ (2+κ)*(a*mean) + κ*r₀ := by
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2+κ by linarith)
    nlinarith
  calc
    _ ≤ P + C.card * (θ*(r+R)) := hh
    _ ≤ P + C.card * (θ*((2+κ)*(a*mean) + κ*r₀)) := by
      gcongr
    _ = (1+2*θ*a)*P + θ*κ*a*P + θ*κ*C.card*r₀ := by
      rw [← hmean]; ring

lemma split_charge (C J : Finset V) (d c b : V → ℝ) (u v P : ℝ)
    (hP : ∑ p ∈ C, d p = P)
    (hc : ∀ p ∈ C, p ∈ J → c p ≤ d p + u)
    (hb : ∀ p ∈ C, p ∉ J → b p ≤ d p + v) :
    clusterCharge C J c b ≤ P + (C ∩ J).card*u + (C \ J).card*v := by
  have h := clusterCharge_le C J c b (fun p => d p + if p ∈ J then u else v)
    (fun p hp hj => by simpa only [ite_eq_left hj] using hc p hp hj)
    (fun p hp hj => by simpa only [ite_eq_right hj] using hb p hp hj)
  simp only [Finset.sum_add_distrib, hP, Finset.sum_ite, Finset.filter_mem_eq_inter,
    Finset.filter_notMem_eq_sdiff, Finset.sum_const, nsmul_eq_mul] at h
  linarith

lemma second_coefficient {μ x : ℝ} (_hμ : 0 ≤ μ) (hμ1 : μ ≤ 1/4)
    (hx : x ≤ 1/3) : 3*x + (1-x)*(1+μ) ≤ 2 := by
  have hh := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2-μ by linarith)
  nlinarith

lemma second_covered_precise {E : Type*} (C J : Finset V) (hC : C.Nonempty)
    (H d₀ : V → ℝ) (offers : V → E → ℝ) (X : Finset E) (e : E) (he : e ∈ X)
    (θ κ a₁ a₂ mean r R r₀ P T q x : ℝ)
    (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1) (hκ : 0 ≤ κ)
    (hown : ∀ p ∈ C, offers p e = d₀ p)
    (hH : ∀ p ∈ C, p ∉ J → H p ≤ d₀ p + a₁*mean + T/(q*C.card))
    (hmean : mean * C.card = P) (hP : ∑ p ∈ C, d₀ p = P)
    (hr : r ≤ a₂*mean) (hR : R ≤ (1+κ)*r + κ*r₀)
    (hx : (C ∩ J).card = x * (C.card : ℝ)) :
    clusterCharge C J (fun p => d₀ p + θ*(r+R))
      (fun p => baseCharge θ (H p) (offers p) X) ≤
      P + θ*(2*a₂*x+(1-x)*a₁)*P + θ*κ*a₂*x*P +
        θ*κ*x*C.card*r₀ + θ*(1-x)*T/q := by
  have hn : (0 : ℝ) < C.card := Nat.cast_pos.mpr hC.card_pos
  have hcount : ((C \ J).card : ℝ) = (1-x)*C.card := by
    have hh : ((C \ J).card : ℝ) + (C ∩ J).card = C.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter C J
    rw [hx] at hh
    linarith
  have hrR : r+R ≤ (2+κ)*(a₂*mean) + κ*r₀ := by
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2+κ by linarith)
    nlinarith
  have hh := split_charge C J d₀ (fun p => d₀ p + θ*(r+R))
    (fun p => baseCharge θ (H p) (offers p) X)
    (θ*((2+κ)*(a₂*mean) + κ*r₀)) (θ*(a₁*mean + T/(q*C.card))) P hP
    (fun p _ _ => by gcongr)
    (fun p hp hj => by
      have h := baseCharge_le_center ht0 ht1 (H p) (offers p) X e he
        (a₁*mean + T/(q*C.card)) (by rw [hown p hp]; linarith [hH p hp hj])
      simpa only [hown p hp] using h)
  apply hh.trans_eq
  rw [hx, hcount, ← hmean]
  field_simp
  ring

lemma second_covered {E : Type*} (C J : Finset V) (hC : C.Nonempty)
    (H d₀ : V → ℝ) (offers : V → E → ℝ) (X : Finset E) (e : E) (he : e ∈ X)
    (θ κ μ mean r R r₀ P T q x : ℝ)
    (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1) (hκ : 0 ≤ κ)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1/4) (hP0 : 0 ≤ P) (hq : 0 < q) (hT : 0 ≤ T)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/3)
    (hown : ∀ p ∈ C, offers p e = d₀ p)
    (hH : ∀ p ∈ C, p ∉ J → H p ≤ d₀ p + (1+μ)*mean + T/(q*C.card))
    (hmean : mean * C.card = P) (hP : ∑ p ∈ C, d₀ p = P)
    (hr : r ≤ (3/2 : ℝ)*mean) (hR : R ≤ (1+κ)*r + κ*r₀)
    (hx : (C ∩ J).card = x * (C.card : ℝ)) :
    clusterCharge C J (fun p => d₀ p + θ*(r+R))
      (fun p => baseCharge θ (H p) (offers p) X) ≤
      (1+2*θ)*P + θ*κ*(3/2)*x*P + θ*κ*x*C.card*r₀ + T/q := by
  have hh := second_covered_precise C J hC H d₀ offers X e he θ κ (1+μ) (3/2)
    mean r R r₀ P T q x ht0 ht1 hκ hown hH hmean hP hr hR hx
  have hcoeff : 2*(3/2 : ℝ)*x + (1-x)*(1+μ) ≤ 2 := by
    nlinarith [second_coefficient hμ hμ1 hx1]
  have hmain := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff ht0) hP0
  have hf : θ*(1-x) ≤ 1 := by
    nlinarith [mul_nonneg ht0 hx0]
  have hterr : θ*(1-x)*T/q ≤ T/q := by
    simpa only [mul_div_assoc, one_mul] using
      mul_le_mul_of_nonneg_right hf (div_nonneg hT hq.le)
  linarith

@[simp] lemma clusterCharge_empty (J : Finset V) (c b : V → ℝ) :
    clusterCharge ∅ J c b = 0 := by simp [clusterCharge]

lemma intersection_fraction_mono (C J J₀ : Finset V) (hJ : J ⊆ J₀) :
    ((C ∩ J).card : ℝ) / C.card ≤ ((C ∩ J₀).card : ℝ) / C.card := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left hJ)

lemma uncovered_large {E : Type*} (C J J₀ : Finset V) (hC : C.Nonempty) (hJ : J ⊆ J₀)
    (H H₀ d₀ : V → ℝ) (offers : V → E → ℝ) (X : Finset E)
    (θ a mean P T q : ℝ) (ht1 : θ ≤ 1) (ha : 0 ≤ a) (hq : 0 < q) (hT : 0 ≤ T)
    (hd : ∀ p ∈ C, 0 ≤ d₀ p) (hP : ∑ p ∈ C, d₀ p = P)
    (hmean : mean * C.card = P)
    (hmono : ∀ p ∈ C, H p ≤ H₀ p)
    (hH : ∀ p ∈ C, H p ≤ d₀ p + a*mean + T/(q*C.card))
    (hf : (C.card : ℝ)/3 ≤ (C ∩ J₀).card) :
    clusterCharge C J d₀ (fun p => baseCharge θ (H p) (offers p) X) ≤
      (1+(2/3 : ℝ)*a)*P + T/q + ∑ p ∈ C ∩ (J₀ \ J), H₀ p := by
  have hn : (0 : ℝ) < C.card := Nat.cast_pos.mpr hC.card_pos
  have hmean0 : 0 ≤ mean := by
    have hh : 0 ≤ mean * C.card := by rw [hmean, ← hP]; exact Finset.sum_nonneg hd
    exact nonneg_of_mul_nonneg_left hh hn
  have hcard : ((C \ J₀).card : ℝ) ≤ (2/3 : ℝ)*C.card := by
    have hh : ((C \ J₀).card : ℝ) + (C ∩ J₀).card = C.card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter C J₀
    linarith
  have hcard' : ((C \ J₀).card : ℝ) ≤ C.card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := C) (t := J₀))
  have hh := clusterCharge_le C J d₀ (fun p => baseCharge θ (H p) (offers p) X)
    (fun p => d₀ p + (if p ∈ J₀ then 0 else a*mean+T/(q*C.card)) +
      if p ∈ J₀ \ J then H₀ p else 0)
    (fun p _ hj => by simp [hj, hJ hj])
    (fun p hp hj => by
      have hb := baseCharge_le_base ht1 (H p) (offers p) X
      by_cases hj₀ : p ∈ J₀
      · simp only [Finset.mem_sdiff, hj₀, hj, not_false_eq_true,
          and_self, ↓reduceIte, add_zero]
        linarith [hmono p hp, hd p hp]
      · simp only [Finset.mem_sdiff, hj₀, false_and, ↓reduceIte, add_zero]
        linarith [hH p hp])
  simp only [Finset.sum_add_distrib, hP, Finset.sum_ite, Finset.filter_mem_eq_inter,
    Finset.filter_notMem_eq_sdiff, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul,
    zero_add, add_zero] at hh
  calc
    _ ≤ P + (C \ J₀).card*(a*mean + T/(q*C.card)) +
        ∑ p ∈ C ∩ (J₀ \ J), H₀ p := by simpa only [mul_add] using hh
    _ = P + (C \ J₀).card*(a*mean) + (C \ J₀).card*(T/(q*C.card)) +
        ∑ p ∈ C ∩ (J₀ \ J), H₀ p := by ring
    _ ≤ P + ((2/3 : ℝ)*C.card)*(a*mean) + C.card*(T/(q*C.card)) +
        ∑ p ∈ C ∩ (J₀ \ J), H₀ p := by
      exact add_le_add (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard
        (mul_nonneg ha hmean0))) (mul_le_mul_of_nonneg_right hcard' (by positivity))) le_rfl
    _ = (1+(2/3 : ℝ)*a)*P + T/q + ∑ p ∈ C ∩ (J₀ \ J), H₀ p := by
      rw [← hmean]
      field_simp

lemma uncovered_small {E : Type*} (C J : Finset V) (hC : C.Nonempty)
    (H d₀ : V → ℝ) (offers : V → E → ℝ) (X : Finset E)
    (θ a mean P T q : ℝ) (ht1 : θ ≤ 1) (ha : 0 ≤ a) (hq : 0 < q) (hT : 0 ≤ T)
    (hd : ∀ p ∈ C, 0 ≤ d₀ p) (hP : ∑ p ∈ C, d₀ p = P)
    (hH : ∀ p ∈ C, H p ≤ d₀ p + a*mean + T/(q*C.card)) :
    clusterCharge C J d₀ (fun p => baseCharge θ (H p) (offers p) X) ≤
      (1+(2/3 : ℝ)*a)*P + T/q +
        ∑ p ∈ (C.filter (fun p => d₀ p ≤ (3/2 : ℝ)*mean)) \ J, H p := by
  classical
  have hn : (0 : ℝ) < C.card := Nat.cast_pos.mpr hC.card_pos
  let N := C.filter (fun p => d₀ p ≤ (3/2 : ℝ)*mean)
  have hN : N ⊆ C := Finset.filter_subset _ _
  have hqterm : 0 ≤ T / (q*C.card) := by positivity
  have hcoeff : 0 ≤ 1+(2/3 : ℝ)*a := by positivity
  have hh := clusterCharge_le C J d₀ (fun p => baseCharge θ (H p) (offers p) X)
    (fun p => (1+(2/3 : ℝ)*a)*d₀ p + T/(q*C.card) + if p ∈ N \ J then H p else 0)
    (fun p hp hj => by
      simp only [Finset.mem_sdiff, hj, not_true_eq_false, and_false, ↓reduceIte, add_zero]
      nlinarith [mul_nonneg ha (hd p hp)])
    (fun p hp hj => by
      have hb := baseCharge_le_base ht1 (H p) (offers p) X
      by_cases hnear : d₀ p ≤ (3/2 : ℝ)*mean
      · have hn : p ∈ N \ J := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hp, hnear⟩, hj⟩
        rw [ite_eq_left hn]
        linarith [mul_nonneg hcoeff (hd p hp)]
      · have hn : p ∉ N \ J := fun hh => hnear (Finset.mem_filter.mp (Finset.mem_sdiff.mp hh).1).2
        rw [ite_eq_right hn, add_zero]
        have hfar : mean ≤ (2/3 : ℝ)*d₀ p := by linarith
        have ha' := mul_le_mul_of_nonneg_left hfar ha
        linarith [hH p hp])
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hP, Finset.sum_ite,
    Finset.filter_mem_eq_inter, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul,
    add_zero, Finset.inter_eq_right.mpr (Finset.sdiff_subset.trans hN)] at hh
  have hdiv : (C.card : ℝ)*(T/(q*C.card)) = T/q := by field_simp
  rw [hdiv] at hh
  exact hh

end MetricKMedianRecovery.RefinedRecovery.Analysis

end OAI
