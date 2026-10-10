import Mathlib
import OAI.Geometry.Cannon.Uniformization.AnnulusFamily
import OAI.Geometry.Cannon.Conformal.SpherePathConnected
import OAI.Geometry.Cannon.Modulus.ModulusSerialBound

namespace OAI

section
section
section
namespace CannonUniformization
open Set Metric unitInterval CannonDuality CannonCells CannonCharts

noncomputable section
variable {X : Type*} [MetricSpace X]

def layerFamily (o : X) (s : ℝ) : Set (Set X) :=
  {A | ∃ u v : X, ∃ p : Path u v, A = range p ∧
    dist u o = s ∧ dist v o = 2*s ∧ ∀ t, dist (p t) o ∈ Icc s (2*s)}

theorem exists_layer_transfer_constant (Q : ℕ) (CP K c : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q CP)
    (hCP : 0 ≤ CP) (hK : 0 < K) (hc : 0 < c) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {ι β : Type*} [Fintype ι] [Fintype β]
      (q : ι → X) (ξ : β → X) (h : X ≃ₜ X) (o : X) (r s d : ℝ),
      0 < r → 0 < s → r ≤ s/2 → d ≤ c →
      max (2+2*K) (max c 1)*(r/s) ≤ 1 →
      (∀ i j, i ≠ j → r ≤ dist (q i) (q j)) →
      (∀ x, ∃ i, dist (q i) x ≤ r) →
      (∀ i j, i ≠ j → r/s ≤ dist (ξ i) (ξ j)) →
      (∀ x y, dist x o ≤ 3*s → dist y o ≤ 3*s →
        c/s*dist x y ≤ dist (h x) (h y) ∧ dist (h x) (h y) ≤ K/s*dist x y) →
      ∀ ω : Weights β,
      Admissible (familyVectors (fun j => ball (ξ j) (2*(r/s))) (macroFamily d) :
        Set (Weights β)) ω →
      ∃ w : Weights ι,
        Admissible (familyVectors (fun i => ball (q i) (2*r)) (layerFamily o s) :
          Set (Weights ι)) w ∧
        (∀ i, dist (q i) o < s/2 ∨ 3*s < dist (q i) o → w i = 0) ∧
        ‖w‖^2 ≤ E*‖ω‖^2 := by
  classical
  obtain ⟨E,hE,hbound⟩ := CannonCapacity.exists_local_transfer_constant Q CP (2+2*K) c
    hpack hCP (by linarith) hc
  refine ⟨E,hE,?_⟩
  intro ι β _ _ q ξ h o r s d hr hs hrs hdc hscale hq hcover hξ hexp ω hω
  have hnω := (admissible_iff _ _ _).mp hω
  let band (i : ι) : Prop := s/2 ≤ dist (q i) o ∧ dist (q i) o ≤ 3*s
  let rel (i : ι) : Finset β := if band i then
    Finset.univ.filter (fun j => dist (ξ j) (h (q i)) ≤ (2+2*K)*(r/s)) else ∅
  let w : Weights ι := WithLp.toLp 2 (fun i => ∑ j ∈ rel i, ω j)
  have hwpoint (i : ι) : w i = ∑ j ∈ rel i, ω j := rfl
  have hw0 (i : ι) : 0 ≤ w i := Finset.sum_nonneg (fun j _ => hnω.1 j)
  refine ⟨w,?_,?_,?_⟩
  · rw [admissible_iff]
    refine ⟨hw0,?_⟩
    rintro A ⟨u,v,p,rfl,hu,hv,hp⟩
    have huB : dist u o ≤ 3*s := by rw [hu]; linarith
    have hvB : dist v o ≤ 3*s := by rw [hv]; linarith
    have hsep : s ≤ dist u v := by
      have hh := dist_triangle v u o
      rw [hu,hv,dist_comm v u] at hh
      linarith
    have hmacro : h '' range p ∈ macroFamily d := by
      refine ⟨h ∘ p,h.continuous.comp p.continuous,?_,?_⟩
      · exact Set.range_comp h p |>.symm
      · have hdiam : dist (h u) (h v) ≤ diam (h '' range p) :=
          dist_le_diam_of_mem ((isCompact_range p.continuous).image h.continuous).isBounded
            ⟨u,⟨0,p.source⟩,rfl⟩ ⟨v,⟨1,p.target⟩,rfl⟩
        have hh := (hexp u v huB hvB).1
        have hmul := mul_le_mul_of_nonneg_left hsep (div_nonneg hc.le hs.le)
        have hid : c/s*s=c := div_mul_cancel₀ c hs.ne'
        rw [hid] at hmul
        exact hdc.trans (hmul.trans (hh.trans hdiam))
    have hline := hnω.2 (h '' range p) hmacro
    have hcharge : ∀ j ∈ indices (fun j => ball (ξ j) (2*(r/s))) (h '' range p),
        ∃ i ∈ indices (fun i => ball (q i) (2*r)) (range p), j ∈ rel i := by
      intro j hj
      obtain ⟨z,⟨x,⟨t,rfl⟩,rfl⟩,hz⟩ := (mem_indices _ _ _).mp hj
      obtain ⟨i,hi⟩ := hcover (p t)
      have hiB : band i := by
        have htri := dist_triangle (p t) (q i) o
        have htri' := dist_triangle (q i) (p t) o
        rw [dist_comm (p t) (q i)] at htri
        dsimp only [band]
        constructor <;> linarith [(hp t).1,(hp t).2]
      refine ⟨i,(mem_indices _ _ _).mpr ⟨p t,mem_range_self t,?_⟩,?_⟩
      · change dist (p t) (q i) < 2*r
        rw [dist_comm]
        linarith
      · change j ∈ if band i then _ else _
        rw [ite_eq_left hiB,Finset.mem_filter]
        refine ⟨Finset.mem_univ _,?_⟩
        have hxB : dist (p t) o ≤ 3*s := by linarith [(hp t).2]
        have hmap := (hexp (q i) (p t) hiB.2 hxB).2
        have hmul := mul_le_mul_of_nonneg_left hi (div_nonneg hK.le hs.le)
        have hz' : dist (ξ j) (h (p t)) < 2*(r/s) := by simpa only [mem_ball,dist_comm] using hz
        have ht := dist_triangle (ξ j) (h (p t)) (h (q i))
        rw [dist_comm (h (p t)) (h (q i))] at ht
        have hnon : 0 ≤ K*(r/s) := mul_nonneg hK.le (div_nonneg hr.le hs.le)
        have hid : K/s*r=K*(r/s) := by ring
        rw [hid] at hmul
        nlinarith
    exact hline.trans (CannonAnnular.finite_charge_cover _ _ rel ω hnω.1 hcharge)
  · intro i hi
    rw [hwpoint]
    have hn : ¬ band i := by rcases hi with hi | hi <;> intro hh <;> linarith [hh.1,hh.2]
    simp [rel,hn]
  · have hb := hbound q ξ h o r s hr hs hscale hq hξ (fun x y hx hy => (hexp x y hx hy).1) ω
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    apply le_trans _ hb
    apply Finset.sum_le_sum
    intro i _
    rw [hwpoint]
    by_cases hi : band i
    · simp only [rel,ite_eq_left hi,ite_eq_left hi.2,le_refl]
    · simp only [rel,ite_eq_right hi,Finset.sum_empty,zero_pow (by omega : 2 ≠ 0)]
      exact sq_nonneg _

end
end CannonUniformization

namespace CannonUniformization
open Set Metric unitInterval CannonDuality CannonCells CannonCharts

noncomputable section
variable {X : Type*} [MetricSpace X]

theorem annulus_modulus_serial {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]
    (q : ι → X) (o : X) (mesh r R : ℝ) (s : J → ℝ)
    (hs : ∀ j, 0 < s j) (hinner : ∀ j, r ≤ s j) (houter : ∀ j, 2*s j ≤ R)
    (hdisj : ∀ j k, j ≠ k → 3*s j < s k/2 ∨ 3*s k < s j/2)
    (w : J → Weights ι)
    (hw : ∀ j, Admissible (familyVectors (fun i => ball (q i) (2*mesh))
      (layerFamily o (s j)) : Set (Weights ι)) (w j))
    (hws : ∀ j i, dist (q i) o < s j/2 ∨ 3*s j < dist (q i) o → w j i = 0)
    {B : ℝ} (hE : ∀ j, ‖w j‖^2 ≤ B) :
    modulus (fun i => ball (q i) (2*mesh)) (annulusFamily o r R) ≤ B/(Fintype.card J : ℝ) := by
  apply modulus_serial_uniform _ _ (fun j => layerFamily o (s j)) w hw ?_ ?_ hE
  · intro i j k hjk
    by_cases hj : w j i = 0
    · rw [hj,zero_mul]
    by_cases hk : w k i = 0
    · rw [hk,mul_zero]
    have hjlo : s j/2 ≤ dist (q i) o := le_of_not_gt (fun hh => hj (hws j i (.inl hh)))
    have hjhi : dist (q i) o ≤ 3*s j := le_of_not_gt (fun hh => hj (hws j i (.inr hh)))
    have hklo : s k/2 ≤ dist (q i) o := le_of_not_gt (fun hh => hk (hws k i (.inl hh)))
    have hkhi : dist (q i) o ≤ 3*s k := le_of_not_gt (fun hh => hk (hws k i (.inr hh)))
    rcases hdisj j k hjk with hh | hh <;> linarith
  · rintro A ⟨u,v,p,rfl,hu,hv⟩ j
    obtain ⟨x,y,t,ht,hx,hy,_,hbet⟩ := CannonAnnular.radial_subpath o u v p (s j) (2*s j)
      (by linarith [hs j]) (hu.trans (hinner j)) ((houter j).trans hv)
    exact ⟨range t,⟨x,y,t,rfl,hx,hy,hbet⟩,ht⟩

theorem exists_annulus_transfer_constant (Q : ℕ) (CP K c : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q CP)
    (hCP : 0 ≤ CP) (hK : 0 < K) (hc : 0 < c) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {ι J : Type*} [Fintype ι] [Fintype J] [Nonempty J]
      (β : J → Type*) [∀ j, Fintype (β j)]
      (q : ι → X) (ξ : ∀ j, β j → X) (h : J → X ≃ₜ X)
      (o : X) (mesh r R d B : ℝ) (s : J → ℝ),
      0 < mesh → (∀ j, 0 < s j) → (∀ j, mesh ≤ s j/2) → d ≤ c →
      (∀ j, max (2+2*K) (max c 1)*(mesh/s j) ≤ 1) →
      (∀ i j, i ≠ j → mesh ≤ dist (q i) (q j)) →
      (∀ x, ∃ i, dist (q i) x ≤ mesh) →
      (∀ j i k, i ≠ k → mesh/s j ≤ dist (ξ j i) (ξ j k)) →
      (∀ j x y, dist x o ≤ 3*s j → dist y o ≤ 3*s j →
        c/s j*dist x y ≤ dist (h j x) (h j y) ∧ dist (h j x) (h j y) ≤ K/s j*dist x y) →
      (∀ j, r ≤ s j) → (∀ j, 2*s j ≤ R) →
      (∀ j k, j ≠ k → 3*s j < s k/2 ∨ 3*s k < s j/2) →
      (∀ j, ∃ ω : Weights (β j),
        Admissible (familyVectors (fun i => ball (ξ j i) (2*(mesh/s j))) (macroFamily d) :
          Set (Weights (β j))) ω ∧ ‖ω‖^2 ≤ B) →
      modulus (fun i => ball (q i) (2*mesh)) (annulusFamily o r R) ≤ E*B/(Fintype.card J : ℝ) := by
  classical
  obtain ⟨E,hE,htrans⟩ := exists_layer_transfer_constant Q CP K c hpack hCP hK hc
  refine ⟨E,hE,?_⟩
  intro ι J _ _ _ β _ q ξ h o mesh r R d B s hm hs hms hd hscale hq hcover hξ hexp hi ho hdisj hω
  choose ω hωadm hωE using hω
  have hweights (j : J) : ∃ w : Weights ι,
      Admissible (familyVectors (fun i => ball (q i) (2*mesh)) (layerFamily o (s j)) :
        Set (Weights ι)) w ∧
      (∀ i, dist (q i) o < s j/2 ∨ 3*s j < dist (q i) o → w i = 0) ∧ ‖w‖^2 ≤ E*B := by
    obtain ⟨w,hw,hws,hwE⟩ := htrans q (ξ j) (h j) o mesh (s j) d hm (hs j) (hms j)
      hd (hscale j) hq hcover (hξ j) (hexp j) (ω j) (hωadm j)
    exact ⟨w,hw,hws,hwE.trans (mul_le_mul_of_nonneg_left (hωE j) hE)⟩
  choose w hw hws hwE using hweights
  exact annulus_modulus_serial q o mesh r R s hs hi ho hdisj w hw hws hwE

end
end CannonUniformization

namespace CannonUniformization
open Set Metric Filter Topology unitInterval CannonDuality CannonCells CannonCharts

noncomputable section

lemma inverse_power_ratio {a : ℝ} (ha : 0 < a) {k m : ℕ} (hkm : k ≤ m) :
    (a^m)⁻¹/(a^k)⁻¹ = (a^(m-k))⁻¹ := by
  have he : a^m=a^(m-k)*a^k := by rw [← pow_add,Nat.sub_add_cancel hkm]
  rw [he,mul_inv]
  field_simp

lemma inverse_power_antitone {a : ℝ} (ha : 1 < a) {k m : ℕ} (hkm : k ≤ m) :
    (a^m)⁻¹ ≤ (a^k)⁻¹ := by
  exact inv_le_inv₀ (pow_pos (zero_lt_one.trans ha) _) (pow_pos (zero_lt_one.trans ha) _)
    |>.mpr (pow_le_pow_right₀ ha.le hkm)

lemma spaced_inverse_powers {a : ℝ} (ha : 1 < a) (ℓ k₀ : ℕ) (hℓ : 8 ≤ a^ℓ)
    {j k : ℕ} (hjk : j < k) :
    3*(a^(k₀+ℓ*k))⁻¹ < (a^(k₀+ℓ*j))⁻¹/2 := by
  have hp : 0 < (a^(k₀+ℓ*j))⁻¹ := inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _)
  have hs : (a^(k₀+ℓ*k))⁻¹ ≤ (a^(k₀+ℓ*j+ℓ))⁻¹ :=
    inverse_power_antitone ha (by
      have hh := Nat.add_le_add_left (Nat.mul_le_mul_left ℓ (Nat.succ_le_of_lt hjk)) k₀
      simpa only [Nat.mul_succ,Nat.add_assoc] using hh)
  have he : (a^(k₀+ℓ*j+ℓ))⁻¹=(a^(k₀+ℓ*j))⁻¹*(a^ℓ)⁻¹ := by rw [pow_add,mul_inv]
  have hi : (a^ℓ)⁻¹ ≤ (8:ℝ)⁻¹ := (inv_le_inv₀ (pow_pos (zero_lt_one.trans ha) ℓ) (by norm_num : (0:ℝ) < 8)).mpr hℓ
  rw [he] at hs
  have hh := hs.trans (mul_le_mul_of_nonneg_left hi hp.le)
  norm_num at hh
  linarith

variable {X : Type*} [MetricSpace X] [PathConnectedSpace X]

theorem annular_modulus_decay (Q : ℕ) (CP L a : ℝ)
    (hpack : CannonPacking.PolynomialPacking (X:=X) Q CP) (hCP : 0 ≤ CP)
    (hL : 1 ≤ L) (ha : 1 < a)
    (hsim : ∀ o : X, ∀ s : ℝ, 0 < s → s ≤ diam (univ : Set X) →
      ∃ f : X ≃ₜ X, ∀ x ∈ ball o s, ∀ y ∈ ball o s,
        dist (f x) (f y)*s ≤ L*dist x y ∧ dist x y ≤ L*dist (f x) (f y)*s)
    (ι : ℕ → Type*) [∀ m, Fintype (ι m)] (p : ∀ m, ι m → X)
    (hpsep : ∀ m i j, i ≠ j → (a^m)⁻¹ ≤ dist (p m i) (p m j))
    (hpnet : ∀ m x, ∃ i, dist (p m i) x ≤ (a^m)⁻¹)
    (d B : ℝ) (hd : 0 < d) (hdiam : d < diam (univ : Set X)) (hdL : d ≤ 1/(4*L))
    (hB : ∀ m, modulus (fun i => ball (p m i) (2*(a^m)⁻¹)) (macroFamily d) ≤ B) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ ℓ k₀ n : ℕ, 8 ≤ a^ℓ →
      4*(a^k₀)⁻¹ ≤ diam (univ : Set X) →
      ∀ᶠ m : ℕ in atTop, ∀ o : X,
        modulus (fun i => ball (p m i) (2*(a^m)⁻¹))
          (annulusFamily o (a^(k₀+ℓ*n))⁻¹ (2*(a^k₀)⁻¹)) ≤ E*B/(n+1:ℝ) := by
  classical
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hap : 0 < a := zero_lt_one.trans ha
  have hc : 0 < 1/(4*L) := by positivity
  obtain ⟨E,hE,htrans⟩ := exists_annulus_transfer_constant Q CP L (1/(4*L)) hpack hCP hLp hc
  refine ⟨E,hE,?_⟩
  intro ℓ k₀ n hℓ hk₀
  let k (j : Fin (n+1)) := k₀+ℓ*j.val
  let s (j : Fin (n+1)) : ℝ := (a^(k j))⁻¹
  have hs (j : Fin (n+1)) : 0 < s j := inv_pos.mpr (pow_pos hap _)
  have hk (j : Fin (n+1)) : k j ≤ k₀+ℓ*n :=
    Nat.add_le_add_left (Nat.mul_le_mul_left ℓ (Nat.le_of_lt_succ j.isLt)) k₀
  have hsmall (j : Fin (n+1)) : s j ≤ (a^k₀)⁻¹ := inverse_power_antitone ha (by dsimp [k]; omega)
  have hlim : Tendsto (fun m : ℕ => (a^m)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr hap).le
      (inv_lt_one_of_one_lt₀ ha)
  have ht (j : Fin (n+1)) : ∀ᶠ m : ℕ in atTop,
      (a^m)⁻¹ ≤ s j/2 ∧ max (2+2*L) (max (1/(4*L)) 1)*((a^m)⁻¹/s j) ≤ 1 := by
    have h₁ := hlim.eventually (eventually_lt_nhds (show 0 < s j/2 by positivity))
    have h₂lim : Tendsto (fun m : ℕ => max (2+2*L) (max (1/(4*L)) 1)*((a^m)⁻¹/s j))
        atTop (𝓝 0) := by simpa using (hlim.div_const (s j)).const_mul (max (2+2*L) (max (1/(4*L)) 1))
    have h₂ := h₂lim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))
    exact (h₁.and h₂).mono (fun _ hh => ⟨hh.1.le,hh.2.le⟩)
  have htall : ∀ᶠ m : ℕ in atTop, ∀ j : Fin (n+1),
      (a^m)⁻¹ ≤ s j/2 ∧ max (2+2*L) (max (1/(4*L)) 1)*((a^m)⁻¹/s j) ≤ 1 :=
    Filter.eventually_all.mpr ht
  filter_upwards [htall,eventually_ge_atTop (k₀+ℓ*n)] with m hm hmge
  intro o
  have hexists (j : Fin (n+1)) : ∃ f : X ≃ₜ X, ∀ x y,
      dist x o ≤ 3*s j → dist y o ≤ 3*s j →
      (1/(4*L))/s j*dist x y ≤ dist (f x) (f y) ∧
        dist (f x) (f y) ≤ L/s j*dist x y := by
    obtain ⟨f,hf⟩ := hsim o (4*s j) (by positivity)
      ((mul_le_mul_of_nonneg_left (hsmall j) (by norm_num)).trans hk₀)
    refine ⟨f,?_⟩
    intro x y hx hy
    have hh := hf x (show x ∈ ball o (4*s j) by change dist x o < _; linarith [hs j])
      y (show y ∈ ball o (4*s j) by change dist y o < _; linarith [hs j])
    constructor
    · have hid : (1/(4*L))/s j*dist x y=dist x y/(L*(4*s j)) := by ring
      rw [hid,div_le_iff₀ (mul_pos hLp (by positivity))]
      nlinarith [hh.2]
    · rw [div_mul_eq_mul_div,le_div_iff₀ (hs j)]
      have hn := mul_nonneg (dist_nonneg (x:=f x) (y:=f y)) (hs j).le
      nlinarith [hh.1]
  choose f hf using hexists
  let β (j : Fin (n+1)) := ι (m-k j)
  let ξ (j : Fin (n+1)) : β j → X := p (m-k j)
  have hratio (j : Fin (n+1)) : (a^m)⁻¹/s j=(a^(m-k j))⁻¹ :=
    inverse_power_ratio hap ((hk j).trans hmge)
  have htarget (j : Fin (n+1)) : ∃ ω : Weights (β j),
      Admissible (familyVectors (fun i => ball (ξ j i) (2*((a^m)⁻¹/s j))) (macroFamily d) :
        Set (Weights (β j))) ω ∧ ‖ω‖^2 ≤ B := by
    obtain ⟨_,ω,hω,hωE⟩ := modulus_minimum
      (fun i => ball (p (m-k j) i) (2*(a^(m-k j))⁻¹)) (by
        intro x
        obtain ⟨i,hi⟩ := hpnet (m-k j) x
        refine ⟨i,?_⟩
        change dist x (p (m-k j) i) < _
        rw [dist_comm]
        have hh : 0 < (a^(m-k j))⁻¹ := by positivity
        linarith) (macroFamily_nonempty hd hdiam)
          (fun A hA => by obtain ⟨p,_,rfl,_⟩ := hA; exact range_nonempty p)
    refine ⟨ω,?_,hωE.le.trans (hB (m-k j))⟩
    simpa only [ξ,hratio] using hω
  have hres := htrans β (p m) ξ f o (a^m)⁻¹ (a^(k₀+ℓ*n))⁻¹ (2*(a^k₀)⁻¹) d B s
    (by positivity) hs (fun j => (hm j).1) hdL (fun j => (hm j).2) (hpsep m) (hpnet m)
    (fun j i l hil => by rw [hratio]; exact hpsep _ i l hil) hf
    (fun j => inverse_power_antitone ha (hk j))
    (fun j => mul_le_mul_of_nonneg_left (hsmall j) (by norm_num))
    (fun j l hjl => by
      rcases lt_or_gt_of_ne (show j.val ≠ l.val from fun he => hjl (Fin.ext he)) with hh | hh
      · exact Or.inr (spaced_inverse_powers ha ℓ k₀ hℓ hh)
      · exact Or.inl (spaced_inverse_powers ha ℓ k₀ hℓ hh)) htarget
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hres

end
end CannonUniformization

end
end
end

end OAI
