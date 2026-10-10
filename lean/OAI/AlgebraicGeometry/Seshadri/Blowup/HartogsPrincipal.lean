import Mathlib

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Hartogs
noncomputable section
variable {A : Type*} [CommRing A] [IsDomain A]

lemma regular_pair_pow_left (x y : A) (hx : x ≠ 0)
    (hxy : ∀ a : A, x ∣ y * a → x ∣ a) (n : ℕ) :
    ∀ a : A, x ^ n ∣ y * a → x ^ n ∣ a := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro a ha
    have hxa : x ∣ a := hxy a ((dvd_pow_self x (Nat.succ_ne_zero n)).trans ha)
    obtain ⟨b, rfl⟩ := hxa
    have hb : x ^ n ∣ y * b := by
      rw [pow_succ, mul_comm (x ^ n) x] at ha
      have hleft : y * (x * b) = x * (y * b) := by ring
      rw [hleft, mul_dvd_mul_iff_left hx] at ha
      exact ha
    obtain ⟨c, hc⟩ := ih b hb
    refine ⟨c, ?_⟩
    rw [hc, pow_succ]
    ring

lemma regular_pair_powers (x y : A) (hx : x ≠ 0)
    (hxy : ∀ a : A, x ∣ y * a → x ∣ a) (n m : ℕ) :
    ∀ a : A, x ^ n ∣ y ^ m * a → x ^ n ∣ a := by
  induction m with
  | zero => simp
  | succ m ih =>
    intro a ha
    apply ih
    apply regular_pair_pow_left x y hx hxy n
    simpa only [pow_succ', mul_assoc] using ha

theorem principal_regular_pair_saturation (x y f a : A) (hx : x ≠ 0)
    (hxy : ∀ b : A, x ∣ y * b → x ∣ b)
    (n m : ℕ) (hn : f ∣ x ^ n * a) (hm : f ∣ y ^ m * a) : f ∣ a := by
  by_cases hf : f = 0
  · subst f
    rw [zero_dvd_iff] at hn ⊢
    exact (mul_eq_zero.mp hn).resolve_left (pow_ne_zero _ hx)
  obtain ⟨b, hb⟩ := hn
  obtain ⟨c, hc⟩ := hm
  have he : y ^ m * b = x ^ n * c := by
    apply mul_left_cancel₀ hf
    calc
      f * (y ^ m * b) = y ^ m * (x ^ n * a) := by rw [hb]; ring
      _ = x ^ n * (y ^ m * a) := by ring
      _ = f * (x ^ n * c) := by rw [hc]; ring
  have hb' : x ^ n ∣ b := regular_pair_powers x y hx hxy n m b ⟨c, he⟩
  obtain ⟨d, hd⟩ := hb'
  refine ⟨d, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero n hx)
  rw [hb, hd]
  ring

theorem principal_quotient_localizations_jointly_injective (x y f : A) (hx : x ≠ 0)
    (hxy : ∀ b : A, x ∣ y * b → x ∣ b) :
    let B := A ⧸ Ideal.span {f}
    let q := Ideal.Quotient.mk (Ideal.span {f})
    Function.Injective ((algebraMap B (Localization.Away (q x))).prod
      (algebraMap B (Localization.Away (q y)))) := by
  dsimp only
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  change (_, _) = (0, 0) at hz
  have hx0 := congrArg Prod.fst hz
  have hy0 := congrArg Prod.snd hz
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers
    (Ideal.Quotient.mk (Ideal.span {f}) x)) _ _).mp hx0
  obtain ⟨v, hv⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers
    (Ideal.Quotient.mk (Ideal.span {f}) y)) _ _).mp hy0
  obtain ⟨n, hn⟩ := u.property
  obtain ⟨m, hm⟩ := v.property
  rw [← hn] at hu
  dsimp only at hu
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hu
  rw [← hm] at hv
  dsimp only at hv
  rw [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hv
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton.mpr (principal_regular_pair_saturation x y f a hx hxy n m hu hv))

end
end MaximalSeshadri.Hartogs
end


end
end

end OAI
