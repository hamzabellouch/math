import OAI.Geometry.NodalSets.Coefficients.CorrectionProductBounds
import OAI.Geometry.NodalSets.Coefficients.RoundSupportedCorrection
import OAI.Geometry.NodalSets.Elliptic.RoundQuotientBounds

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem round_correction_size {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (r : ℕ) {A : ℝ} (hA : 0 < A) :
    ∃ C > 0, ∀ (u R H : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ u → ContDiff ℝ ∞ R →
      tsupport R ⊆ Q → (∀ x, 0 < H x) → ∀ (n : ℕ), 0 < n → ∀ eps : ℝ, 0 < eps →
      (∀ x ∈ Q, ∀ i, i ≤ r+2 → ‖iteratedFDeriv ℝ i u x‖ ≤ A*(n:ℝ)^(i+3)*H x) →
      (∀ x ∈ Q, ∀ i, i ≤ r+1 → ‖iteratedFDeriv ℝ i R x‖ ≤ eps*H x) →
      (∀ x ∈ Q, ((n:ℝ)^65)⁻¹*H x ≤ sourceFirstJetSize u n x) →
      let f := fun x ↦ R x / roundCorrectionDenominator u n x
      let alpha := fun x ↦ f x*u x
      let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
      tsupport alpha ⊆ tsupport R ∧ tsupport beta ⊆ tsupport R ∧
      ∀ x i, i ≤ r → ‖iteratedFDeriv ℝ i alpha x‖ + ‖iteratedFDeriv ℝ i beta x‖ ≤
        C*eps*(n:ℝ)^(137*r+267) := by
  obtain ⟨F,hF,hquot⟩ := round_quotient_finite_bound hQ (r+1) hA
  obtain ⟨G,hG,hmul⟩ := compact_multiplier_frequency_bound roundCoordFactor roundCoordFactor_smooth hQ (r+1)
  obtain ⟨D,hD,hdiv⟩ := weighted_divergence_finite_frequency_bound roundCoordDensity
    roundCoordDensity_smooth (fun x ↦ (roundCoordDensity_pos x).ne') hQ r
  let L : ℝ := (2:ℝ)^(r+1)*F*A
  refine ⟨2*L+D*G*L,by dsimp [L]; positivity,?_⟩
  intro u R H hu hR hs hH n hn eps heps hub hRb hjet
  let f := fun x ↦ R x / roundCorrectionDenominator u n x
  obtain ⟨hf,hfc,hfs,hfb⟩ := hquot u R H hu hR hs hH n hn eps heps
    (fun x hx i hi ↦ hub x hx i (by omega)) hRb hjet
  let alpha := fun x ↦ f x*u x
  let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
  have ha : ContDiff ℝ ∞ alpha := hf.mul hu
  have hbeta : ContDiff ℝ ∞ beta := Yau.densityCorrection_smooth roundCoordDensity_smooth
    (fun x ↦ (roundCoordDensity_pos x).ne') hu hf
    (fun i ↦ contDiff_pi.mp (roundCoordGradient_smooth u hu) i) _
  have has : tsupport alpha ⊆ tsupport R := by
    apply (show tsupport alpha ⊆ tsupport f from ?_).trans hfs
    apply closure_mono
    intro x hx
    exact fun h ↦ hx (by simp [alpha,h])
  have hbs : tsupport beta ⊆ tsupport R :=
    (Yau.densityCorrection_tsupport_subset _ _ _ _ _).trans hfs
  refine ⟨hf,ha,hbeta,has,hbs,?_⟩
  intro x i hi
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hNpos : (0:ℝ) < n := by exact_mod_cast hn
  have hHx := hH x
  have hL : 0 < L := by dsimp [L]; positivity
  by_cases hx : x ∈ Q
  · have hp (j : Fin 4) : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ u y (Pi.single j 1)) :=
      (hu.fderiv_right (by simp)).clm_apply contDiff_const
    have haBound (j : ℕ) (hj : j ≤ r+1) :
        ‖iteratedFDeriv ℝ j alpha x‖ ≤ L*eps*(n:ℝ)^(137*j+131) := by
      have h := correction_product_bound f u hf hu x j 3 hN (mul_nonneg hF.le heps.le) hA.le hHx
        (fun k hk ↦ hfb x k (by omega)) (fun k hk ↦ hub x hx k (by omega))
      calc
        _ ≤ (2:ℝ)^(r+1)*(F*eps)*A*(n:ℝ)^(137*j+128+3) := by
          exact h.trans (by gcongr; norm_num)
        _ = _ := by dsimp [L]; congr 1; ring
    have hpBound (l : Fin 4) (j : ℕ) (hj : j ≤ r+1) :
        ‖iteratedFDeriv ℝ j (fun y ↦ f y*fderiv ℝ u y (Pi.single l 1)) x‖ ≤
          L*eps*(n:ℝ)^(137*j+132) := by
      have hvb (k : ℕ) (hk : k ≤ j) :
          ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ u y (Pi.single l 1)) x‖ ≤
            A*(n:ℝ)^(k+4)*H x :=
        (real_partial_iterated_bound u hu x l k).trans (by
          simpa [Nat.add_assoc] using hub x hx (k+1) (by omega))
      have h := correction_product_bound f _ hf (hp l) x j 4 hN
        (mul_nonneg hF.le heps.le) hA.le hHx (fun k hk ↦ hfb x k (by omega)) hvb
      calc
        _ ≤ (2:ℝ)^(r+1)*(F*eps)*A*(n:ℝ)^(137*j+128+4) := by
          exact h.trans (by gcongr; norm_num)
        _ = _ := by dsimp [L]; congr 1; ring
    let V := fun y l ↦ f y*roundCoordGradient u y l
    have hV (l : Fin 4) : ContDiff ℝ ∞ (fun y ↦ V y l) :=
      hf.mul (contDiff_pi.mp (roundCoordGradient_smooth u hu) l)
    have hvb (l : Fin 4) (j : ℕ) (hj : j ≤ r+1) :
        ‖iteratedFDeriv ℝ j (fun y ↦ V y l) x‖ ≤ (G*L*eps)*(n:ℝ)^(137*j+132) := by
      have he : (fun y ↦ V y l) = fun y ↦ roundCoordFactor y*(f y*fderiv ℝ u y (Pi.single l 1)) := by
        funext y; dsimp [V,roundCoordGradient]; ring
      rw [he]
      have h := hmul _ (hf.mul (hp l)) n (L*eps) hN (by positivity) 132 x hx (hpBound l) j hj
      convert h using 1
      first | rfl | ring
    have hd := hdiv V hV n (G*L*eps) hN (by positivity) 132 x hx hvb i hi
    have hlam : (n:ℝ)^2 ≤ seedEigenvalue n := by unfold seedEigenvalue; nlinarith
    have hlam0 : 0 < seedEigenvalue n := lt_of_lt_of_le (by positivity) hlam
    have hlaminv : (seedEigenvalue n)⁻¹ ≤ ((n:ℝ)^2)⁻¹ :=
      (inv_le_inv₀ hlam0 (by positivity)).mpr hlam
    have hds : ContDiff ℝ ∞ (Yau.weightedDiv roundCoordDensity V) :=
      Yau.weightedDiv_smooth roundCoordDensity_smooth (fun y ↦ (roundCoordDensity_pos y).ne') hV
    have hterm : ‖iteratedFDeriv ℝ i (fun y ↦ (seedEigenvalue n)⁻¹*Yau.weightedDiv roundCoordDensity V y) x‖ ≤
        (D*G*L)*eps*(n:ℝ)^(137*i+267) := by
      change ‖iteratedFDeriv ℝ i ((seedEigenvalue n)⁻¹ • Yau.weightedDiv roundCoordDensity V) x‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply (hds.of_le
        (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt,
        norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hlam0)]
      calc
        _ ≤ ((n:ℝ)^2)⁻¹*(D*(G*L*eps)*(n:ℝ)^(137*i+132+137)) := by gcongr
        _ = _ := by
          rw [show 137*i+132+137 = 2+(137*i+267) by omega,pow_add]
          field_simp
    have hb : ‖iteratedFDeriv ℝ i beta x‖ ≤ (L+D*G*L)*eps*(n:ℝ)^(137*r+267) := by
      change ‖iteratedFDeriv ℝ i (fun y ↦ alpha y - (seedEigenvalue n)⁻¹*Yau.weightedDiv roundCoordDensity V y) x‖ ≤ _
      rw [fun_iteratedFDeriv_sub_apply (ha.of_le
        (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt
        ((contDiff_const.mul hds).of_le
          (by exact_mod_cast (show (i:ℕ∞) ≤ ⊤ from le_top))).contDiffAt]
      have h := (norm_sub_le _ _).trans (add_le_add (haBound i (by omega)) hterm)
      refine h.trans ?_
      calc
        _ ≤ L*eps*(n:ℝ)^(137*r+267)+(D*G*L)*eps*(n:ℝ)^(137*r+267) := by gcongr; omega
        _ = _ := by ring
    have hab : ‖iteratedFDeriv ℝ i alpha x‖ ≤ L*eps*(n:ℝ)^(137*r+267) :=
      (haBound i (by omega)).trans (by gcongr; omega)
    have h := add_le_add hab hb
    convert h using 1
    first | rfl | ring
  · have hax : x ∉ tsupport alpha := fun h ↦ hx (hs (has h))
    have hbx : x ∉ tsupport beta := fun h ↦ hx (hs (hbs h))
    rw [((notMem_tsupport_iff_eventuallyEq.mp hax).iteratedFDeriv ℝ i).eq_of_nhds,
      ((notMem_tsupport_iff_eventuallyEq.mp hbx).iteratedFDeriv ℝ i).eq_of_nhds]
    simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero,zero_add]
    positivity

end
end Yau.Target

end OAI
