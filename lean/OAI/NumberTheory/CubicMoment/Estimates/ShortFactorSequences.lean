import OAI.NumberTheory.CubicMoment.Estimates.TruncatedLargeValues

namespace OAI

/-! The actual all-short families cannot have an unsaved moment sequence. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def ShortFactorFamily.comp {ι : Type*} (F : ShortFactorFamily ι) (φ : ℕ → ℕ) :
    ShortFactorFamily ι where
  cutoff := F.cutoff ∘ φ
  length := F.length ∘ φ
  coefficient := F.coefficient ∘ φ
  twist := F.twist ∘ φ
  factor_spec := fun j i => F.factor_spec (φ j) i
  length_ge_one := fun j i => F.length_ge_one (φ j) i
  twist_bound := fun j i => F.twist_bound (φ j) i

@[simp] lemma ShortFactorFamily.comp_cubicValue {ι : Type*} (F : ShortFactorFamily ι)
    (φ : ℕ → ℕ) (j : ℕ) (i : ι) (x : Eisenstein) :
    (F.comp φ).cubicValue j i x = F.cubicValue (φ j) i x := rfl

@[simp] lemma ShortFactorFamily.comp_mixedValue {ι : Type*} (F : ShortFactorFamily ι)
    (φ : ℕ → ℕ) (j : ℕ) (i : ι) (x : Eisenstein × Eisenstein) :
    (F.comp φ).mixedValue j i x = F.mixedValue (φ j) i x := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Compactness produces the length exponents too. Thus the subsequent
moment argument does not assume either the value or the length limits. -/
theorem ShortFactorFamily.lengths_subsequence (F : ShortFactorFamily ι)
    {Y : ℕ → ℝ} {δ : ℝ} (_hY : Tendsto Y atTop atTop) (hY₁ : ∀ j, 1 < Y j)
    (hshort : ∀ j i, F.length j i ≤ (Y j)^(1-δ))
    (htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1) :
    ∃ (φ : ℕ → ℕ) (a : ι → ℝ), StrictMono φ ∧
      (∀ i, 0 ≤ a i ∧ a i ≤ 1-δ) ∧ (∑ i, a i = 1) ∧
      ∀ i, HasPowerExponent (Y ∘ φ) (fun j => F.length (φ j) i) (a i) := by
  have hb (j : ℕ) (i : ι) : 0 ≤ Real.log (F.length j i)/Real.log (Y j) ∧
      Real.log (F.length j i)/Real.log (Y j) ≤ 1-δ :=
    logarithmic_power_bounds (hY₁ j) (by simpa using F.length_ge_one j i) (hshort j i)
  obtain ⟨a,φ,hφ,ha,hexp⟩ := bounded_logarithms_subsequence Y
    (fun i j => F.length j i) (fun _ => 0) (fun _ => 1-δ) hb
  have hprod := HasPowerExponent.prod_natPowers (fun _ : ι => 1) hexp
    (fun i => Eventually.of_forall (fun j => zero_lt_one.trans_le (F.length_ge_one (φ j) i)))
  simp only [Nat.cast_one,one_mul,pow_one] at hprod
  have htotal' : HasPowerExponent (Y ∘ φ) (fun j => ∏ i, F.length (φ j) i) 1 :=
    htotal.comp hφ.tendsto_atTop
  exact ⟨φ,a,hφ,ha,tendsto_nhds_unique hprod htotal',hexp⟩

/-- With a fixed gap below length one, an actual first-configuration
moment cannot remain at exponent `7/3`. All subsequences are constructed. -/
theorem ShortFactorFamily.first_unsaved_sequence_impossible (F : ShortFactorFamily ι)
    (Y G : ℕ → ℝ) (S : ℕ → Finset Eisenstein) {δ H D : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hY : Tendsto Y atTop atTop) (hY₂ : ∀ j, 2 ≤ Y j)
    (hG : ∀ j, 1 ≤ G j) (hGexp : HasPowerExponent Y G (7/3))
    (hS : ∀ j, ∀ p ∈ S j, gramDyad (Y j) p)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hshort : ∀ j i, F.length j i ≤ (Y j)^(1-δ))
    (htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1)
    (hbound : ∀ j, ∀ p ∈ S j, ∀ i, ‖F.cubicValue j i p‖ ≤ (Y j)^H)
    (hmoment : ∀ j, G j ≤ ∑ p ∈ S j, ‖∏ i, F.cubicValue j i p‖^2) : False := by
  obtain ⟨φ,a,hφ,ha,hasum,haexp⟩ := F.lengths_subsequence hY
    (fun j => by linarith [hY₂ j]) hshort htotal
  let K : ℝ := D/2+(Fintype.card ι:ℝ)*H+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcut : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2 := by dsimp [K]; linarith
  have hGφ : HasPowerExponent (Y ∘ φ) (G ∘ φ) (7/3) := hGexp.comp hφ.tendsto_atTop
  obtain ⟨ψ,P,B,r,v,hψ,hP,hB,hrow,hRexp,hVexp,_,_,hlarge⟩ :=
    extract_unsaved_moment_subsequence (Y ∘ φ) (G ∘ φ) (S ∘ φ)
      (fun j i p => ‖F.cubicValue (φ j) i p‖) hH hK hcut
      (hY.comp hφ.tendsto_atTop) (fun j => hY₂ (φ j)) (fun j => hG (φ j)) hGφ
      (fun j => hcard (φ j)) (fun _ _ _ _ => _root_.norm_nonneg _)
      (fun j => hbound (φ j)) (fun j => by simpa only [norm_prod,Function.comp_def] using hmoment (φ j))
  have hYφψ : Tendsto ((Y ∘ φ) ∘ ψ) atTop atTop :=
    (hY.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hNexp : HasPowerExponent ((Y ∘ φ) ∘ ψ) ((Y ∘ φ) ∘ ψ) 1 := by
    simpa only [Real.rpow_one] using HasPowerExponent.variable_rpow hYφψ
      (tendsto_const_nhds (x := (1:ℝ)))
  apply ((F.comp φ).comp ψ).first_rows_contradiction P B hYφψ
    (fun j => by simpa only [Function.comp_def] using (show 1 ≤ Y (φ (ψ j)) by linarith [hY₂ (φ (ψ j))]))
    (fun j p hp => hS (φ (ψ j)) p ((hP j).2 hp))
    (fun j => (hP j).1)
    (fun j i => (Real.rpow_pos_of_pos (by simpa only [Function.comp_def] using
      (show 0 < Y (φ (ψ j)) by linarith [hY₂ (φ (ψ j))])) _).trans_le (hB j i).1)
    (fun j p hp i => (hrow j p hp i).1) hRexp hNexp
    (fun i => (haexp i).comp hψ.tendsto_atTop) hVexp
    (fun i => lt_of_le_of_lt (ha i).2 (by linarith)) hasum (by linarith)


/-- The balanced actual short-factor family also cannot retain an unsaved
moment; its row and value limits are extracted inside the proof. -/
theorem ShortFactorFamily.balanced_unsaved_sequence_impossible (F : ShortFactorFamily ι)
    (hHuxley : HuxleyAdditiveLargeSieve) (Y G : ℕ → ℝ)
    (S : ℕ → Finset (Eisenstein × Eisenstein)) {δ H D : ℝ}
    (hδ : 0 < δ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hY : Tendsto Y atTop atTop) (hY₂ : ∀ j, 2 ≤ Y j)
    (hG : ∀ j, 1 ≤ G j) (hGexp : HasPowerExponent Y G (7/3))
    (hS : ∀ j, ∀ p ∈ S j, PrimarySquarefreePair p ∧
      norm p.1 ≤ (Y j)^(1/3:ℝ) ∧ norm p.2 ≤ (Y j)^(1/3:ℝ))
    (hcard : ∀ j, ((S j).card:ℝ) ≤ (Y j)^D)
    (hshort : ∀ j i, F.length j i ≤ (Y j)^(1-δ))
    (htotal : HasPowerExponent Y (fun j => ∏ i, F.length j i) 1)
    (hbound : ∀ j, ∀ p ∈ S j, ∀ i, ‖F.mixedValue j i p‖ ≤ (Y j)^H)
    (hmoment : ∀ j, G j ≤ ∑ p ∈ S j, ‖∏ i, F.mixedValue j i p‖^2) : False := by
  obtain ⟨φ,a,hφ,ha,hasum,haexp⟩ := F.lengths_subsequence hY
    (fun j => by linarith [hY₂ j]) hshort htotal
  let K : ℝ := D/2+(Fintype.card ι:ℝ)*H+1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcut : D+2*(Fintype.card ι:ℝ)*H-2*K ≤ -2 := by dsimp [K]; linarith
  have hGφ : HasPowerExponent (Y ∘ φ) (G ∘ φ) (7/3) := hGexp.comp hφ.tendsto_atTop
  obtain ⟨ψ,P,B,r,v,hψ,hP,hB,hrow,hRexp,hVexp,_,_,hlarge⟩ :=
    extract_unsaved_moment_subsequence (Y ∘ φ) (G ∘ φ) (S ∘ φ)
      (fun j i p => ‖F.mixedValue (φ j) i p‖) hH hK hcut
      (hY.comp hφ.tendsto_atTop) (fun j => hY₂ (φ j)) (fun j => hG (φ j)) hGφ
      (fun j => hcard (φ j)) (fun _ _ _ _ => _root_.norm_nonneg _)
      (fun j => hbound (φ j)) (fun j => by simpa only [norm_prod,Function.comp_def] using hmoment (φ j))
  let Z : ℕ → ℝ := (Y ∘ φ) ∘ ψ
  have hZ : Tendsto Z atTop atTop := (hY.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hZ₁ (j : ℕ) : 1 ≤ Z j := by dsimp [Z]; linarith [hY₂ (φ (ψ j))]
  have hZp (j : ℕ) : 0 < Z j := zero_lt_one.trans_le (hZ₁ j)
  have hQexp : HasPowerExponent Z (fun j => (Z j)^(2/3:ℝ)) (2/3) :=
    HasPowerExponent.variable_rpow hZ tendsto_const_nhds
  have hLexp : HasPowerExponent Z (fun j => (Z j)^(1/3:ℝ)) (1/3) :=
    HasPowerExponent.variable_rpow hZ tendsto_const_nhds
  have hP' (j : ℕ) (p : Eisenstein × Eisenstein) (hp : p ∈ P j) :
      PrimarySquarefreePair p ∧ norm (pairConductor p) ≤ (Z j)^(2/3:ℝ) := by
    have hs := hS (φ (ψ j)) p ((hP j).2 hp)
    refine ⟨hs.1,?_⟩
    rw [pairConductor,norm_mul_eq]
    calc
      _ ≤ (Z j)^(1/3:ℝ)*(Z j)^(1/3:ℝ) :=
        mul_le_mul hs.2.1 hs.2.2 (norm_nonneg _) (Real.rpow_nonneg (hZp j).le _)
      _ = _ := by rw [← Real.rpow_add (hZp j)]; norm_num
  apply ((F.comp φ).comp ψ).balanced_rows_contradiction hHuxley P B hZ
    (fun j => Real.one_le_rpow (hZ₁ j) (by norm_num))
    (fun j => Real.one_le_rpow (hZ₁ j) (by norm_num)) hP'
    (fun j p hp => (hS (φ (ψ j)) p ((hP j).2 hp)).2)
    (fun j => (hP j).1)
    (fun j i => (Real.rpow_pos_of_pos (hZp j) (-K)).trans_le (hB j i).1)
    (fun j p hp i => (hrow j p hp i).1) hRexp hQexp hLexp
    (fun i => (haexp i).comp hψ.tendsto_atTop) hVexp
    (fun i => lt_of_le_of_lt (ha i).2 (by linarith)) hasum (by linarith)

end CubicFirstMoment

end

end OAI
