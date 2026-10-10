import OAI.Algebra.FormalGroup.Honda.Coordinates

namespace OAI

noncomputable section

namespace HeightThree.HondaCoordinates
open MvPowerSeries HondaConstruction HondaTarget LogarithmicConstruction PTypical
variable {R S : Type*} [CommRing R] [CommRing S]

def killFirstFun (f : MvPowerSeries (Fin 2) R) : MvPowerSeries (Fin 2) R :=
  fun d => if d 0 = 0 then coeff d f else 0

@[simp] lemma coeff_killFirstFun (f : MvPowerSeries (Fin 2) R) (d : Fin 2 →₀ ℕ) :
    coeff d (killFirstFun f) = if d 0 = 0 then coeff d f else 0 := rfl

def killFirst : MvPowerSeries (Fin 2) R →ₐ[R] MvPowerSeries (Fin 2) R where
  toFun := killFirstFun
  map_one' := by
    ext d
    change (if d 0 = 0 then coeff d (1 : MvPowerSeries (Fin 2) R) else 0) = _
    by_cases h : d 0 = 0
    · simp [h]
    · have hd : d ≠ 0 := by intro he; simp [he] at h
      simp [h, hd, coeff_one]
  map_mul' f g := by
    let : DecidableEq (Fin 2) := Classical.decEq _
    ext d
    change (if d 0 = 0 then coeff d (f*g) else 0) = _
    rw [coeff_mul]
    by_cases hd : d 0 = 0
    · rw [ite_eq_left hd, coeff_mul]
      apply Finset.sum_congr rfl
      rintro ⟨a,b⟩ hab
      have hab' := congrArg (fun x : Fin 2 →₀ ℕ => x 0) (Finset.HasAntidiagonal.mem_antidiagonal.mp hab)
      have ha : a 0 = 0 := by simp only [Finsupp.add_apply] at hab'; omega
      have hb : b 0 = 0 := by simp only [Finsupp.add_apply] at hab'; omega
      simp only [coeff_killFirstFun, ha, hb, ite_true]
    · rw [ite_eq_right hd]
      symm
      apply Finset.sum_eq_zero
      rintro ⟨a,b⟩ hab
      have hab' := congrArg (fun x : Fin 2 →₀ ℕ => x 0) (Finset.HasAntidiagonal.mem_antidiagonal.mp hab)
      change (if a 0 = 0 then coeff a f else 0) *
        (if b 0 = 0 then coeff b g else 0) = 0
      by_cases ha : a 0 = 0
      · have hb : b 0 ≠ 0 := by simp only [Finsupp.add_apply] at hab'; omega
        simp [hb]
      · simp [ha]
  map_zero' := by ext d; simp
  map_add' f g := by
    ext d
    change (if d 0 = 0 then coeff d (f+g) else 0) = _
    rw [map_add]
    by_cases h : d 0 = 0 <;> simp [h]
  commutes' r := by
    ext d
    change (if d 0 = 0 then coeff d (C r : MvPowerSeries (Fin 2) R) else 0) = coeff d (C r)
    by_cases h : d 0 = 0
    · simp [h]
    · have hd : d ≠ 0 := by intro he; simp [he] at h
      simp [h, hd, coeff_C]

@[simp] lemma coeff_killFirst (f : MvPowerSeries (Fin 2) R) (d : Fin 2 →₀ ℕ) :
    coeff d (killFirst f) = if d 0 = 0 then coeff d f else 0 := rfl

@[simp] lemma killFirst_X_zero : killFirst (X 0 : MvPowerSeries (Fin 2) R) = 0 := by
  ext d
  rw [coeff_killFirst]
  by_cases h : d 0 = 0
  · have hd : d ≠ Finsupp.single 0 1 := by intro he; simp [he] at h
    simp [h, coeff_X, hd]
  · simp [h]

@[simp] lemma killFirst_X_one : killFirst (X 1 : MvPowerSeries (Fin 2) R) = X 1 := by
  ext d
  rw [coeff_killFirst]
  by_cases h : d 0 = 0
  · simp [h]
  · have hd : d ≠ Finsupp.single 1 1 := by intro he; simp [he] at h
    simp [h, coeff_X, hd]

lemma killFirst_eq_zero_iff (f : MvPowerSeries (Fin 2) R) :
    killFirst f = 0 ↔ f ∈ Ideal.span ({X 0} : Set (MvPowerSeries (Fin 2) R)) := by
  rw [Ideal.mem_span_singleton, X_dvd_iff]
  constructor
  · intro h d hd
    have hc := congrArg (coeff d) h
    simpa [hd] using hc
  · intro h
    ext d
    by_cases hd : d 0 = 0 <;> simp [hd, h]

lemma map_killFirst (φ : R →+* S) (f : MvPowerSeries (Fin 2) R) :
    (killFirst f).map φ = killFirst (f.map φ) := by
  ext d
  simp only [coeff_map, coeff_killFirst]
  split_ifs <;> simp

lemma expand_killFirst (p : ℕ) (hp : p ≠ 0) (f : MvPowerSeries (Fin 2) R) :
    expand p hp (killFirst f) = killFirst (expand p hp f) := by
  ext d
  by_cases hd : ∃ e : Fin 2 →₀ ℕ, p • e = d
  · obtain ⟨e, rfl⟩ := hd
    rw [coeff_expand_smul, coeff_killFirst, coeff_killFirst, coeff_expand_smul]
    congr 1
    simp [Finsupp.smul_apply, smul_eq_mul, hp]
  · have hz (g : MvPowerSeries (Fin 2) R) : coeff d (expand p hp g) = 0 := by
      by_contra h
      have hh := support_expand_subset p hp g h
      exact hd ⟨hh.choose, hh.choose_spec.2⟩
    rw [hz, coeff_killFirst, hz]
    split_ifs <;> rfl

end HeightThree.HondaCoordinates

namespace HeightThree.HondaCoordinates
open MvPowerSeries HondaConstruction HondaTarget LogarithmicConstruction PTypical
variable {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]

lemma formalGroup_map_map (F : FormalGroup A) (α : A →+* B) (β : B →+* C) :
    (F.map α).map β = F.map (β.comp α) := by
  apply FormalGroup.ext
  rfl

lemma formalGroup_map_injective (α : A →+* B) (hα : Function.Injective α) :
    Function.Injective (FormalGroup.map · α) := by
  intro F G h
  apply FormalGroup.ext
  apply map_injective α hα
  exact congrArg FormalGroup.toPowerSeries h

lemma integralFormalGroup_natural [Algebra ℚ B] [Algebra ℚ D]
    (ι : A →+* B) (hι : Function.Injective ι) (κ : C →+* D) (hκ : Function.Injective κ)
    (α : A →+* C) (β : B →ₐ[ℚ] D) (hi : β.toRingHom.comp ι = κ.comp α)
    (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p)
    (ψ' : C →+* C) (χ' : D →ₐ[ℚ] D) (hc' : χ'.toRingHom.comp κ = κ.comp ψ')
    (hψ' : ∀ a : C, (p : C) ∣ ψ' a - a^p)
    (hα : ψ'.comp α = α.comp ψ) (v : Fin 3 → A) :
    (integralFormalGroup ι hι p ψ χ hc hψ v).map α =
      integralFormalGroup κ hκ p ψ' χ' hc' hψ' (α ∘ v) := by
  apply formalGroup_map_injective κ hκ
  dsimp only
  rw [formalGroup_map_map, ← hi, ← formalGroup_map_map, integralFormalGroup_map,
    integralFormalGroup_map, StrictLog.formalGroup_map,
    heightThreeLog_map ι κ α β hi p hp.out.two_le ψ ψ' hα v]

lemma killFirst_inclusion :
    (killFirst (R := ℚ)).toRingHom.comp coefficientInclusion =
      coefficientInclusion.comp (killFirst (R := ℤ)).toRingHom := by
  ext f d
  exact congrArg (coeff d) (map_killFirst (Int.castRingHom ℚ) f).symm

lemma killFirst_commute_integralFrobenius (p : ℕ) (hp : p ≠ 0) :
    (integralFrobenius p hp).comp (killFirst (R := ℤ)).toRingHom =
      (killFirst (R := ℤ)).toRingHom.comp (integralFrobenius p hp) := by
  ext f d
  exact congrArg (coeff d) (expand_killFirst p hp f)

lemma integralHonda_killFirst (p : ℕ) [hp : Fact p.Prime] :
    (integralHonda p).map (killFirst (R := ℤ)).toRingHom =
      integralFormalGroup coefficientInclusion coefficientInclusion_injective p
        (integralFrobenius p hp.out.ne_zero) (rationalFrobenius p hp.out.ne_zero)
        (frobenius_compatible p hp.out.ne_zero) (integralFrobenius_congr p)
        (killFirst ∘ parameters) := by
  exact integralFormalGroup_natural _ _ _ _ _ _ killFirst_inclusion p _ _ _ _ _ _ _ _
    (killFirst_commute_integralFrobenius p hp.out.ne_zero) parameters

lemma integralHonda_height_two (p : ℕ) [hp : Fact p.Prime] :
    (∀ j < p^2, killFirst ((multiplicationSeries (integralHonda p) p).coeff j) =
      (p : IntegralBase) * (PowerSeries.X : PowerSeries IntegralBase).coeff j) ∧
    killFirst ((multiplicationSeries (integralHonda p) p).coeff (p^2)) =
      X 1 * (1-(p : IntegralBase)^(p^2-1)) := by
  have h := integralFormalGroup_height_two coefficientInclusion coefficientInclusion_injective p
    (integralFrobenius p hp.out.ne_zero) (rationalFrobenius p hp.out.ne_zero)
    (frobenius_compatible p hp.out.ne_zero) (integralFrobenius_congr p)
    (killFirst ∘ parameters) (by simp [parameters])
  rw [← integralHonda_killFirst, multiplication_map] at h
  constructor
  · intro j hj
    exact h.1 j hj
  · convert h.2 using 1 <;> simp [parameters]

theorem reducedHonda_height_one (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [CommRing K] [CharP K p] :
    (∀ j < p, (multiplicationSeries (reducedHonda p K) p).coeff j = 0) ∧
    (multiplicationSeries (reducedHonda p K) p).coeff p = X 0 := by
  have h := integralFormalGroup_height_one coefficientInclusion coefficientInclusion_injective p
    (integralFrobenius p hp.out.ne_zero) (rationalFrobenius p hp.out.ne_zero)
    (frobenius_compatible p hp.out.ne_zero) (integralFrobenius_congr p) parameters
  change (∀ j < p, (multiplicationSeries (integralHonda p) p).coeff j = _) ∧
    (multiplicationSeries (integralHonda p) p).coeff p = parameters 0 * (1-(p : IntegralBase)^(p-1)) at h
  have hpc : (p : MvPowerSeries (Fin 2) K) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg
      (MvPowerSeries.C (σ := Fin 2)) (CharP.cast_eq_zero K p)
  simp only [reducedHonda, multiplication_map, PowerSeries.coeff_map]
  constructor
  · intro j hj
    rw [h.1 j hj, map_mul, map_natCast, hpc, zero_mul]
  · rw [h.2]
    simp only [map_mul, map_sub, map_one, map_pow, map_natCast, hpc,
      parameters, Matrix.cons_val_zero, map_X, zero_pow (by have := hp.out.two_le; omega : p-1 ≠ 0), sub_zero,
      mul_one]

theorem reducedHonda_heightCoordinates (p : ℕ) [hp : Fact p.Prime]
    (K : Type*) [CommRing K] [CharP K p] :
    HeightCoordinates p (reducedHonda p K) := by
  have h1 := reducedHonda_height_one p K
  have hpc : (p : MvPowerSeries (Fin 2) K) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg
      (MvPowerSeries.C (σ := Fin 2)) (CharP.cast_eq_zero K p)
  refine ⟨h1.1, h1.2, ?_, ?_⟩
  · intro j hj
    rw [← killFirst_eq_zero_iff]
    simp only [reducedHonda, multiplication_map, PowerSeries.coeff_map]
    rw [← map_killFirst, (integralHonda_height_two p).1 j hj,
      map_mul, map_natCast, hpc, zero_mul]
  · rw [← killFirst_eq_zero_iff, map_sub, killFirst_X_one]
    simp only [reducedHonda, multiplication_map, PowerSeries.coeff_map]
    rw [← map_killFirst, (integralHonda_height_two p).2]
    simp only [map_mul, map_sub, map_one, map_pow, map_natCast, hpc,
      map_X, zero_pow (by have : 1 < p^2 := one_lt_pow₀ hp.out.one_lt (by decide); omega : p^2-1 ≠ 0),
      sub_zero, mul_one, sub_self]

end HeightThree.HondaCoordinates

end

end OAI
