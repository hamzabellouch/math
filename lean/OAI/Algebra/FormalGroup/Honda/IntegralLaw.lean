import OAI.Algebra.FormalGroup.Honda.Logarithm

namespace OAI

noncomputable section

namespace HeightThree.HondaConstruction
open MvPowerSeries PTypical LogarithmicConstruction

variable {A B : Type*} [CommRing A] [CommRing B]

theorem law_integral [Algebra ℚ B] (ι : A →+* B) (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p) (v : Fin 3 → A)
    (l : StrictLog (R := B)) (hf : HasIntegralNumerators ι p l.series)
    (he : defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) l.series = PowerSeries.X) :
    IntegralSeries ι l.law := by
  apply integral_of_defect_log ι p ψ χ hc hψ v l.series hf he l.linear_one _ l.law_constant
  rw [l.log_law, StrictLog.sumSeries, defect_add]
  have hi (i : Fin 2) : IntegralSeries ι
      (defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) (l.series.subst (X i))) := by
    simpa only [map_X] using
      defect_log_integral ι p ψ χ hc hψ v l.series hf he (X i) (by simp)
  exact (hi 0).add ι (hi 1)

lemma map_injective (ι : A →+* B) (hinj : Function.Injective ι) {σ : Type*} :
    Function.Injective (MvPowerSeries.map (σ := σ) ι) := by
  intro f g hfg
  ext d
  apply hinj
  simpa only [coeff_map] using congrArg (coeff d) hfg

def descendFormalGroup (ι : A →+* B) (hinj : Function.Injective ι)
    (F : FormalGroup B) (hF : IntegralSeries ι F.toPowerSeries) : FormalGroup A := by
  let f := integralLift ι F.toPowerSeries hF
  have hf : f.map ι = F.toPowerSeries := map_integralLift ι _ hF
  have hc : f.constantCoeff = 0 := by
    apply hinj
    simpa only [← constantCoeff_map, hf, map_zero] using F.zero_constantCoeff
  refine ⟨f, hc, ?_, ?_, ?_⟩
  · apply hinj
    rw [map_one, ← coeff_map, hf, F.lin_coeff_X]
  · apply hinj
    rw [map_one, ← coeff_map, hf, F.lin_coeff_Y]
  · apply map_injective ι hinj
    have hj (g₁ g₂ : MvPowerSeries (Fin 3) A) :
        ![g₁.map ι, g₂.map ι] = fun i => (![g₁, g₂] i).map ι := by
      ext i; fin_cases i <;> rfl
    rw [map_subst (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 hc),
      map_subst (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 hc)]
    simp_rw [← hj, map_subst HasSubst.X_X, ← hj, map_X, hf]
    exact F.assoc

@[simp] theorem map_descendFormalGroup (ι : A →+* B) (hinj : Function.Injective ι)
    (F : FormalGroup B) (hF : IntegralSeries ι F.toPowerSeries) :
    (descendFormalGroup ι hinj F hF).map ι = F := by
  apply FormalGroup.ext
  exact map_integralLift ι _ hF

instance descendFormalGroup_isComm (ι : A →+* B) (hinj : Function.Injective ι)
    (F : FormalGroup B) [F.IsComm] (hF : IntegralSeries ι F.toPowerSeries) :
    (descendFormalGroup ι hinj F hF).IsComm where
  comm := by
    apply map_injective ι hinj
    have hf : (descendFormalGroup ι hinj F hF).toPowerSeries.map ι = F.toPowerSeries :=
      map_integralLift ι _ hF
    rw [hf, map_subst HasSubst.X_X, hf]
    calc
      F.toPowerSeries = F.toPowerSeries.subst ![X 1, X 0] := FormalGroup.IsComm.comm
      _ = _ := by congr 1; funext i; fin_cases i <;> simp

end HeightThree.HondaConstruction

namespace HeightThree.HondaConstruction
open MvPowerSeries PTypical LogarithmicConstruction
variable {A B : Type*} [CommRing A] [CommRing B]

def numerator (p : ℕ) (ψ : A →+* A) (v : Fin 3 → A) : ℕ → A
  | 0 => 1
  | n+1 => ∑ i : Fin 3, if i.val ≤ n then
      (p : A)^i.val * v i * (ψ^(i.val+1)) (numerator p ψ v (n-i.val)) else 0
termination_by n => n

def logarithm [Algebra ℚ B] (ι : A →+* B) (p : ℕ) (ψ : A →+* A)
    (v : Fin 3 → A) : PowerSeries B :=
  series p (fun n => ((p : ℚ)⁻¹)^n • ι (numerator p ψ v n))

lemma logarithm_constant [Algebra ℚ B] (ι : A →+* B) (p : ℕ) (hp : 2 ≤ p)
    (ψ : A →+* A) (v : Fin 3 → A) :
    (logarithm ι p ψ v).constantCoeff = 0 := series_constant p hp _

lemma logarithm_linear [Algebra ℚ B] (ι : A →+* B) (p : ℕ) (hp : 2 ≤ p)
    (ψ : A →+* A) (v : Fin 3 → A) :
    (logarithm ι p ψ v).coeff 1 = 1 := by
  simp [logarithm, series_linear p hp, numerator]

lemma twisted_series_coeff (p : ℕ) (hp : 2 ≤ p) (χ : B →+* B)
    (c : ℕ → B) (k n : ℕ) :
    PowerSeries.coeff (p^n) ((twist p (by omega) χ ^ k) (series p c)) =
      if k ≤ n then (χ^k) (c (n-k)) else 0 := by
  rw [twist_iterate]
  change PowerSeries.coeff (p^n) (((series p c).map (χ^k)).expand (p^k) _) = _
  rw [PowerSeries.coeff_expand]
  simp only [Nat.pow_dvd_pow_iff_le_right (by omega : 1 < p)]
  split_ifs with h
  · rw [Nat.pow_div h (by omega : 0 < p), PowerSeries.coeff_map,
      coeff_series_power p hp]
  · rfl

lemma twisted_series_coeff_outside (p : ℕ) (hp : 2 ≤ p) (χ : B →+* B)
    (c : ℕ → B) (k j : ℕ) (hj : ¬ ∃ n : ℕ, p^n = j) :
    PowerSeries.coeff j ((twist p (by omega) χ ^ k) (series p c)) = 0 := by
  rw [twist_iterate]
  change PowerSeries.coeff j (((series p c).map (χ^k)).expand (p^k) _) = _
  rw [PowerSeries.coeff_expand]
  split_ifs with h
  · rw [PowerSeries.coeff_map, coeff_series_outside p (j / p^k) c, map_zero]
    rintro ⟨n, hn⟩
    exact hj ⟨k+n, by rw [pow_add, hn, Nat.mul_div_cancel' h]⟩
  · rfl

end HeightThree.HondaConstruction

namespace HeightThree.HondaConstruction
open MvPowerSeries PTypical LogarithmicConstruction
variable {A B : Type*} [CommRing A] [CommRing B]

lemma iterate_smul [Algebra ℚ B] (χ : B →ₐ[ℚ] B) (n : ℕ) (q : ℚ) (b : B) :
    (χ.toRingHom^n) (q • b) = q • ((χ.toRingHom^n) b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change χ ((χ.toRingHom^n) (q • b)) = q • χ ((χ.toRingHom^n) b)
    rw [ih, χ.map_smul_of_tower]

lemma iterate_comp (ι : A →+* B) (ψ : A →+* A) (χ : B →+* B)
    (hc : χ.comp ι = ι.comp ψ) (n : ℕ) (a : A) :
    (χ^n) (ι a) = ι ((ψ^n) a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ' χ, pow_succ' ψ]
    change χ ((χ^n) (ι a)) = ι (ψ ((ψ^n) a))
    rw [ih]
    exact DFunLike.congr_fun hc _

lemma scalar_denominator [Algebra ℚ B] (p : ℕ) (hp : p ≠ 0)
    (n i : ℕ) (hi : i ≤ n) (b : B) :
    ((p : ℚ)⁻¹)^(n+1) • ((p : B)^i * b) =
      (p : ℚ)⁻¹ • (((p : ℚ)⁻¹)^(n-i) • b) := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have he : ((p : ℚ)⁻¹)^(n+1) * (p : ℚ)^i =
      (p : ℚ)⁻¹ * ((p : ℚ)⁻¹)^(n-i) := by
    rw [show n+1 = i + (n-i+1) by omega, pow_add]
    calc
      _ = (((p : ℚ)⁻¹) * p)^i * ((p : ℚ)⁻¹)^(n-i+1) := by ring
      _ = _ := by simp [hpQ, pow_succ, mul_comm]
  have hb : ((p : B)^i * b) = (p : ℚ)^i • b := by
    simp [Algebra.smul_def]
  rw [hb, smul_smul, he, smul_smul]

lemma logarithm_recurrence [Algebra ℚ B] (ι : A →+* B) (p : ℕ) (hp : p ≠ 0)
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (v : Fin 3 → A) (n : ℕ) :
    ((p : ℚ)⁻¹)^(n+1) • ι (numerator p ψ v (n+1)) =
      ∑ i : Fin 3, (p : ℚ)⁻¹ • (ι (v i) *
        (if i.val ≤ n then (χ.toRingHom^(i.val+1))
          (((p : ℚ)⁻¹)^(n-i.val) • ι (numerator p ψ v (n-i.val))) else 0)) := by
  rw [numerator, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rw [map_mul, map_mul, map_pow, map_natCast, mul_assoc,
      scalar_denominator p hp n i.val hi,
      iterate_smul, iterate_comp ι ψ χ.toRingHom hc,
      mul_smul_comm]
  · simp

end HeightThree.HondaConstruction

end

end OAI
