import OAI.Geometry.HeilbronnTriangle.PlaneLowRankCount
import OAI.Geometry.HeilbronnTriangle.SpecialNormals
import OAI.Geometry.HeilbronnTriangle.IntegralPlaneRows

namespace OAI


noncomputable section

namespace Problem355.SpecialRankOneCount

open IntegralPlaneLattice

theorem scalar_bound (a q N I R g J h : ℝ)
    (hq : 1 ≤ q) (_hN : 0 ≤ N) (hI : 0 < I) (hR : 0 < R)
    (hg : 0 < g) (hJ : 0 < J)
    (hcov : I * R / g ≤ J) (hg3 : g ^ 3 ≤ I * h ^ 2)
    (ha : a ≤ (q + 1) * (9 * Real.pi * (4 * N) ^ 2 / (q * J)) ^ 3) :
    a ≤ 2 * (144 * Real.pi) ^ 3 * N ^ 6 * h ^ 2 /
      (q ^ 2 * I ^ 2 * R ^ 3) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hIR : I * R ≤ J * g := (div_le_iff₀ hg).mp hcov
  have hp : I ^ 3 * R ^ 3 ≤ J ^ 3 * g ^ 3 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ I * R) hIR 3
  have hp' : I ^ 3 * R ^ 3 ≤ J ^ 3 * (I * h ^ 2) :=
    hp.trans (mul_le_mul_of_nonneg_left hg3 (by positivity))
  have hden : I ^ 2 * R ^ 3 ≤ J ^ 3 * h ^ 2 := by
    apply (mul_le_mul_iff_right₀ hI).mp
    nlinarith [hp']
  have hinv : (1 : ℝ) / J ^ 3 ≤ h ^ 2 / (I ^ 2 * R ^ 3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul, mul_one, mul_comm] using hden
  have hbase : a ≤ 2 * (144 * Real.pi) ^ 3 * N ^ 6 / (q ^ 2 * J ^ 3) := by
    calc
      a ≤ (q + 1) * (9 * Real.pi * (4 * N) ^ 2 / (q * J)) ^ 3 := ha
      _ ≤ (2 * q) * (9 * Real.pi * (4 * N) ^ 2 / (q * J)) ^ 3 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 2 * (144 * Real.pi) ^ 3 * N ^ 6 / (q ^ 2 * J ^ 3) := by
        field_simp
        ring
  calc
    a ≤ 2 * (144 * Real.pi) ^ 3 * N ^ 6 / (q ^ 2 * J ^ 3) := hbase
    _ = (2 * (144 * Real.pi) ^ 3 * N ^ 6 / q ^ 2) * (1 / J ^ 3) := by ring
    _ ≤ (2 * (144 * Real.pi) ^ 3 * N ^ 6 / q ^ 2) *
        (h ^ 2 / (I ^ 2 * R ^ 3)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * (144 * Real.pi) ^ 3 * N ^ 6 * h ^ 2 /
        (q ^ 2 * I ^ 2 * R ^ 3) := by ring

theorem shell_sum_le (q R : ℕ) [Fact q.Prime] (hR : 0 < R)
    (S : Finset (Fin 3 → ℤ)) (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hbox : ∀ x ∈ S, ∀ t, -((2 * R : ℕ) : ℤ) ≤ x t ∧ x t ≤ ((2 * R : ℕ) : ℤ))
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (z : S → Fin 3 → ℤ) (hz : ∀ x : S, dotProduct x.1 (z x) = 1)
    (L : ∀ x : S, Submodule ℤ (plane x.1))
    [∀ x : S, DiscreteTopology (L x)] [∀ x : S, IsZLattice ℝ (L x)]
    (f : ∀ x : S, L x →+
      (PlaneLines.normalMap (fun t => (x.1 t : ZMod q))).ker)
    (hf : ∀ x : S, Function.Surjective (f x))
    (T : ∀ x : S, Finset (Fin 3 → L x)) (N I h W₀ : ℝ)
    (hN : 0 ≤ N) (hI : 0 < I) (hW₀ : 0 ≤ W₀)
    (hnorm : ∀ (x : S) u, u ∈ T x → ∀ t, ‖(u t : plane x.1)‖ ≤ 4 * N)
    (hspan : ∀ (x : S) u, u ∈ T x →
      Submodule.span ℝ (Set.range (fun t => (u t : plane x.1))) = ⊤)
    (hlow : ∀ (x : S) u, u ∈ T x → Module.finrank (ZMod q)
      (Submodule.span (ZMod q) (Set.range (fun t => f x (u t)))) ≤ 1)
    (g : S → ℝ) (hg : ∀ x, 0 < g x)
    (hg3 : ∀ x, g x ^ 3 ≤ I * h ^ 2)
    (hcov : ∀ x, I * (R : ℝ) / g x ≤ ZLattice.covolume (L x))
    (W : ∀ x : S, (Fin 3 → L x) → ℝ)
    (hW : ∀ (x : S) u, u ∈ T x → W x u ≤ W₀) :
    (∑ x : S, ∑ u ∈ T x, W x u) ≤
      1024 * (144 * Real.pi) ^ 3 * W₀ * N ^ 6 * h ^ 2 /
        ((q : ℝ) ^ 4 * I ^ 2) := by
  classical
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq.ne')
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hred (x : S) : (fun t => (x.1 t : ZMod q)) ≠ 0 := by
    intro he
    have he' : ∀ t, (x.1 t : ZMod q) = 0 := fun t => congr_fun he t
    have hz' := congrArg (fun a : ℤ => (a : ZMod q)) (hz x)
    simp only [dotProduct, Int.cast_sum, Int.cast_mul, he', zero_mul,
      Finset.sum_const_zero, Int.cast_one] at hz'
    exact zero_ne_one hz'
  let B := 2 * (144 * Real.pi) ^ 3 * N ^ 6 * h ^ 2 /
    ((q : ℝ) ^ 2 * I ^ 2 * (R : ℝ) ^ 3)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint (x : S) : ((T x).card : ℝ) ≤ B := by
    have hc := PlaneLowRankCount.card_low_rank_le
      (plane_finrank x.1 (z x) (hz x))
      (PlaneLines.normal_plane_finrank _ (hred x)) (L x) (f x) (hf x)
      (T x) (4 * N) (by positivity) (hnorm x) (hspan x) (hlow x)
    have hc' : ((T x).card : ℝ) ≤ ((q : ℝ) + 1) *
        (9 * Real.pi * (4 * N) ^ 2 / ((q : ℝ) * ZLattice.covolume (L x))) ^ 3 := by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using hc
    exact scalar_bound _ _ N I R (g x) _ h hq1 hN hI hR0 (hg x)
      (ZLattice.covolume_pos (L x) MeasureTheory.volume) (hcov x) (hg3 x) hc'
  have hweight (x : S) : (∑ u ∈ T x, W x u) ≤ W₀ * B := by
    calc
      (∑ u ∈ T x, W x u) ≤ ∑ _u ∈ T x, W₀ :=
        Finset.sum_le_sum (fun u hu => hW x u hu)
      _ = ((T x).card : ℝ) * W₀ := by simp [nsmul_eq_mul]
      _ ≤ B * W₀ := mul_le_mul_of_nonneg_right (hpoint x) hW₀
      _ = W₀ * B := mul_comm _ _
  have hScard : (S.card : ℝ) ≤ 512 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
    have hc := SpecialNormals.card_exceptional_normals_le S (2 * R) q hq i j k
      hki hkj hbox hnonzero hline
    convert hc using 1; push_cast; ring
  calc
    (∑ x : S, ∑ u ∈ T x, W x u) ≤ ∑ _x : S, W₀ * B :=
      Finset.sum_le_sum (fun x _ => hweight x)
    _ = (S.card : ℝ) * (W₀ * B) := by simp [nsmul_eq_mul]
    _ ≤ (512 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2) * (W₀ * B) :=
      mul_le_mul_of_nonneg_right hScard (mul_nonneg hW₀ hB)
    _ = 1024 * (144 * Real.pi) ^ 3 * W₀ * N ^ 6 * h ^ 2 /
        ((q : ℝ) ^ 4 * I ^ 2) := by
      dsimp [B]
      field_simp
      ring

end Problem355.SpecialRankOneCount

end

end OAI
