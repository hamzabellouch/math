import OAI.MathematicalPhysics.AlternatingFlow.Scales

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Encoding

noncomputable def code (b : ℕ) : List ℕ → ℝ
  | [] => 0
  | d :: ds => ((d : ℝ) + code b ds) / b

noncomputable def tailMax (b : ℕ) : ℝ :=
  letI := twoAtLeastTwo
  ((b : ℝ) - 2) / ((b : ℝ) - 1)

lemma tailMax_nonneg (b : ℕ) (hb : 2 ≤ b) : 0 ≤ tailMax b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold tailMax
  exact div_nonneg (by linarith) (by linarith)

lemma tailMax_lt_one (b : ℕ) (hb : 2 ≤ b) : tailMax b < 1 := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  unfold tailMax
  apply (div_lt_one (by linarith)).2
  linarith

lemma tailMax_identity (b : ℕ) (hb : 2 ≤ b) :
    (b : ℝ) * tailMax b = (b : ℝ) - 2 + tailMax b := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have h : (b : ℝ) - 1 ≠ 0 := by linarith
  unfold tailMax
  field_simp
  ring

lemma code_nonneg (b : ℕ) (L : List ℕ) : 0 ≤ code b L := by
  induction L with
  | nil => simp [code]
  | cons d L ih => simpa only [code] using div_nonneg (by positivity) (Nat.cast_nonneg b)

lemma code_le_tailMax (b : ℕ) (hb : 2 ≤ b) (L : List ℕ)
    (hL : ∀ d ∈ L, d + 2 ≤ b) : code b L ≤ tailMax b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  induction L with
  | nil => exact tailMax_nonneg b hb
  | cons d L ih =>
    have hd : (d : ℝ) + 2 ≤ b := by exact_mod_cast hL d (by simp)
    have ht : code b L ≤ tailMax b := ih (fun a ha => hL a (List.mem_cons_of_mem d ha))
    rw [code, div_le_iff₀ hb']
    have hi := tailMax_identity b hb
    linarith

lemma digit_interval (b d : ℕ) (hb : 2 ≤ b) (L : List ℕ)
    (hL : ∀ a ∈ L, a + 2 ≤ b) :
    (d : ℝ) / b ≤ code b (d :: L) ∧ code b (d :: L) ≤ ((d : ℝ) + 1) / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  constructor
  · exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (code_nonneg b L)) hb'.le
  · apply div_le_div_of_nonneg_right _ hb'.le
    linarith [code_le_tailMax b hb L hL, tailMax_lt_one b hb]

lemma code_append (b : ℕ) (hb : 0 < b) (L R : List ℕ) :
    code b (L ++ R) = code b L + ((b : ℝ) ^ L.length)⁻¹ * code b R := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  induction L with
  | nil => simp [code]
  | cons d L ih =>
    simp only [List.cons_append, code, List.length_cons, pow_succ, ih]
    field_simp
    ring

lemma code_denominator (b : ℕ) (hb : 0 < b) (L : List ℕ) :
    ∃ a : ℕ, (b : ℝ) ^ L.length * code b L = a := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  induction L with
  | nil => exact ⟨0, by simp [code]⟩
  | cons d L ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨b ^ L.length * d + a, ?_⟩
    calc
      (b : ℝ) ^ (d :: L).length * code b (d :: L) =
          (b : ℝ) ^ L.length * d + (b : ℝ) ^ L.length * code b L := by
        simp only [List.length_cons, code, pow_succ]
        field_simp
      _ = ((b ^ L.length * d + a : ℕ) : ℝ) := by rw [ha]; push_cast; rfl

lemma configuration_block (b g : ℕ) (hb : 0 < b) (L R : List ℕ) :
    code b (g :: (L ++ R)) =
      ((g : ℝ) + code b L + ((b : ℝ) ^ L.length)⁻¹ * code b R) / b := by
  rw [code, code_append b hb]
  ring

lemma integral_rescale (b k l : ℕ) (hkl : k ≤ l) {x : ℝ}
    (hx : ∃ a : ℤ, (b : ℝ) ^ k * x = a) :
    ∃ a : ℤ, (b : ℝ) ^ l * x = a := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨(b : ℤ) ^ (l - k) * a, ?_⟩
  calc
    (b : ℝ) ^ l * x = (b : ℝ) ^ (l - k) * ((b : ℝ) ^ k * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hkl]
    _ = ((b : ℤ) ^ (l - k) * a : ℤ) := by rw [ha]; push_cast; rfl

lemma sum_integral {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, ∃ a : ℤ, f i = a) : ∃ a : ℤ, ∑ i ∈ S, f i = a := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨a, ha⟩ := hf i (by simp)
    obtain ⟨c, hc⟩ := ih (fun j hj => hf j (by simp [hj]))
    exact ⟨a + c, by simp [Finset.sum_insert hi, ha, hc]⟩

noncomputable def donor (b N : ℕ) (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), if j % 2 = n % 2 then Scales.ε b N j * C j else 0

lemma old_record_integral (b N j n : ℕ) (hb : 0 < b) (hjn : j < n) {C : ℝ}
    (hC : ∃ a : ℤ, (b : ℝ) ^ (1 + 2 * Scales.K N j) * C = a) :
    ∃ a : ℤ, (b : ℝ) ^ Scales.s N n * (Scales.ε b N j * C) = a := by
  apply integral_rescale b (Scales.s N j + (1 + 2 * Scales.K N j))
    (Scales.s N n) (Scales.old_scale_gap N j n hjn)
  obtain ⟨a, ha⟩ := hC
  refine ⟨a, ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  calc
    (b : ℝ) ^ (Scales.s N j + (1 + 2 * Scales.K N j)) * (Scales.ε b N j * C) =
      (b : ℝ) ^ (1 + 2 * Scales.K N j) * C := by
        dsimp [Scales.ε]
        rw [pow_add]
        field_simp
    _ = a := ha

lemma donor_integer_add (b N n : ℕ) (hb : 0 < b) (C : ℕ → ℝ)
    (hC : ∀ j, ∃ a : ℤ, (b : ℝ) ^ (1 + 2 * Scales.K N j) * C j = a) :
    ∃ a : ℤ, (b : ℝ) ^ Scales.s N n * donor b N C n = a + C n := by
  have hI : ∀ j ∈ Finset.range n,
      ∃ a : ℤ, (b : ℝ) ^ Scales.s N n *
        (if j % 2 = n % 2 then Scales.ε b N j * C j else 0) = a := by
    intro j hj
    split_ifs
    · exact old_record_integral b N j n hb (Finset.mem_range.1 hj) (hC j)
    · exact ⟨0, by simp⟩
  obtain ⟨a, ha⟩ := sum_integral (Finset.range n) _ hI
  refine ⟨a, ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  rw [donor, Finset.sum_range_succ]
  simp only [ite_true, mul_add, Finset.mul_sum]
  rw [ha]
  dsimp [Scales.ε]
  field_simp

def DecoderLaw (b : ℕ) (P : ℝ → ℝ) : Prop :=
  Function.Periodic P 1 ∧ ∀ v ∈ Set.Icc 0 (tailMax b), P v = v

lemma decoder_int_add (b : ℕ) (P : ℝ → ℝ) (hP : DecoderLaw b P)
    (a : ℤ) (v : ℝ) (hv : v ∈ Set.Icc 0 (tailMax b)) : P ((a : ℝ) + v) = v := by
  have h := hP.1.int_mul a v
  simpa only [mul_one, add_comm, hP.2 v hv] using h

lemma read_current (b N n : ℕ) (hb : 2 ≤ b) (C : ℕ → ℝ)
    (hC : ∀ j, ∃ a : ℤ, (b : ℝ) ^ (1 + 2 * Scales.K N j) * C j = a)
    (hc : C n ∈ Set.Icc 0 (tailMax b))
    (P : ℝ → ℝ) (hP : DecoderLaw b P) :
    P ((b : ℝ) ^ Scales.s N n * donor b N C n) = C n := by
  obtain ⟨a, ha⟩ := donor_integer_add b N n (by omega) C hC
  rw [ha]
  exact decoder_int_add b P hP a (C n) hc

lemma remove_prefix (b s : ℕ) (hb : 0 < b) (L R : List ℕ) (D : ℝ)
    (hD : ∃ a : ℤ, (b : ℝ) ^ s * D = a + code b (L ++ R)) :
    ∃ a : ℤ, (b : ℝ) ^ (s + L.length) * D = a + code b R := by
  obtain ⟨a, ha⟩ := hD
  obtain ⟨c, hc⟩ := code_denominator b hb L
  refine ⟨(b : ℤ) ^ L.length * a + c, ?_⟩
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  calc
    (b : ℝ) ^ (s + L.length) * D = (b : ℝ) ^ L.length * ((b : ℝ) ^ s * D) := by
      rw [pow_add]; ring
    _ = (b : ℝ) ^ L.length * a + (b : ℝ) ^ L.length * code b L + code b R := by
      rw [ha, code_append b hb]
      field_simp
      ring
    _ = (((b : ℤ) ^ L.length * a + c : ℤ) : ℝ) + code b R := by rw [hc]; push_cast; rfl

lemma read_after_prefix (b s : ℕ) (hb : 2 ≤ b) (L R : List ℕ) (D : ℝ)
    (hD : ∃ a : ℤ, (b : ℝ) ^ s * D = a + code b (L ++ R))
    (hR : ∀ d ∈ R, d + 2 ≤ b) (P : ℝ → ℝ) (hP : DecoderLaw b P) :
    P ((b : ℝ) ^ (s + L.length) * D) = code b R := by
  obtain ⟨a, ha⟩ := remove_prefix b s (by omega) L R D hD
  rw [ha]
  exact decoder_int_add b P hP a _ ⟨code_nonneg b R, code_le_tailMax b hb R hR⟩

lemma read_configuration (b s g : ℕ) (hb : 2 ≤ b) (L R : List ℕ) (D : ℝ)
    (hD : ∃ a : ℤ, (b : ℝ) ^ s * D = a + code b (g :: (L ++ R)))
    (hd : ∀ d ∈ g :: (L ++ R), d + 2 ≤ b)
    (P : ℝ → ℝ) (hP : DecoderLaw b P) :
    P ((b : ℝ) ^ s * D) = code b (g :: (L ++ R)) ∧
    P ((b : ℝ) ^ (s + 1 + L.length) * D) = code b R ∧
    P ((b : ℝ) ^ (s + 1) * D) - ((b : ℝ) ^ L.length)⁻¹ *
      P ((b : ℝ) ^ (s + 1 + L.length) * D) = code b L := by
  have hLR : ∀ d ∈ L ++ R, d + 2 ≤ b :=
    fun d h => hd d (List.mem_cons_of_mem g h)
  have hR : ∀ d ∈ R, d + 2 ≤ b := fun d h => hLR d (List.mem_append_right L h)
  have h₁ := read_after_prefix b s hb [g] (L ++ R) D hD hLR P hP
  have h₂ := read_after_prefix b s hb (g :: L) R D (by simpa using hD) hR P hP
  simp only [List.length_cons, List.length_nil] at h₁ h₂
  have h₂' : P ((b : ℝ) ^ (s + 1 + L.length) * D) = code b R := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h₂
  refine ⟨?_, h₂', ?_⟩
  · obtain ⟨a, ha⟩ := hD
    rw [ha]
    exact decoder_int_add b P hP a _
      ⟨code_nonneg b _, code_le_tailMax b hb _ hd⟩
  · rw [h₁, h₂', code_append b (by omega)]
    ring

end Encoding
end AlternatingNS

namespace AlternatingNS
namespace Encoding

lemma donor_in_plateau (b N n : ℕ) (hb : 4 ≤ b) (C : ℕ → ℝ)
    (hC : ∀ j, C j ∈ Set.Icc (0 : ℝ) 1) :
    donor b N C n ∈ Set.Ico (0 : ℝ) (1 / 4) := by
  have hterm : ∀ j : ℕ,
      0 ≤ (if j % 2 = n % 2 then Scales.ε b N j * C j else 0) ∧
        (if j % 2 = n % 2 then Scales.ε b N j * C j else 0) ≤ Scales.ε b N j := by
    intro j
    have hε := Scales.ε_nonneg b N j (by omega)
    split_ifs
    · exact ⟨mul_nonneg hε (hC j).1, mul_le_of_le_one_right hε (hC j).2⟩
    · exact ⟨le_rfl, hε⟩
  constructor
  · apply Finset.sum_nonneg
    intro j _
    exact (hterm j).1
  · apply lt_of_le_of_lt _ (Scales.initial_memory_small b N hb)
    apply le_trans _ (Scales.total_memory_le b N (by omega))
    calc
      donor b N C n ≤ ∑ j ∈ Finset.range (n + 1), Scales.ε b N j :=
        Finset.sum_le_sum (fun j _ => (hterm j).2)
      _ ≤ ∑' j : ℕ, Scales.ε b N j :=
        (Scales.summable_ε b N (by omega)).sum_le_tsum _
          (fun j _ => Scales.ε_nonneg b N j (by omega))

lemma pop_code (b d : ℕ) (hb : 0 < b) (L : List ℕ) :
    (b : ℝ) * code b (d :: L) - d = code b L := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  dsimp [code]
  field_simp
  ring

lemma tape_step_right (b a w : ℕ) (hb : 0 < b) (L R : List ℕ) :
    (((w : ℝ) + code b L) / b, (b : ℝ) * code b (a :: R) - a) =
      (code b (w :: L), code b R) := by
  rw [pop_code b a hb R]
  rfl

lemma tape_step_stay (b a w : ℕ) (hb : 0 < b) (L R : List ℕ) :
    (code b L, ((w : ℝ) + ((b : ℝ) * code b (a :: R) - a)) / b) =
      (code b L, code b (w :: R)) := by
  rw [pop_code b a hb R]
  rfl

lemma tape_step_left (b a w l : ℕ) (hb : 0 < b) (L R : List ℕ) :
    ((b : ℝ) * code b (l :: L) - l,
      ((l : ℝ) + ((w : ℝ) + ((b : ℝ) * code b (a :: R) - a)) / b) / b) =
      (code b L, code b (l :: w :: R)) := by
  rw [pop_code b l hb L, pop_code b a hb R]
  rfl

end Encoding
end AlternatingNS

end OAI
