import Mathlib
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.LocalContainment
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionCoefficientOrder
import OAI.AlgebraicGeometry.Seshadri.Geometry.ResidualZero

namespace OAI


                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}} [IsIntegral X]

theorem extract_power_with_order (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (d n j : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (t : O X ⟶ (L.pow (d+n)).sheaf) (ht : t ≠ 0)
    (ho : (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v))^(j+1) ∣
      affineCoefficient U (localPowerFrame U.1 e (d+n)) t) :
    ∃ q : O X ⟶ (L.pow n).sheaf, q ≠ 0 ∧
      q ≫ sectionMultiply (L.pow d) (L.pow n) (sectionCombination k s v) ≫
        (linePowerAdd L d n).inv = t ∧
      (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v))^j ∣
        affineCoefficient U (localPowerFrame U.1 e n) q := by
  let f := affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)
  have hf : f ≠ 0 := affineCoefficient_ne_zero (L.pow d) U _ _ hne
  have hv : pullbackSection (sectionIdeal k s hs v).subschemeι t = 0 := by
    apply (pullback_section_zero_iff_local_coefficient p _ (L.pow (d+n)) t U
      (localPowerFrame U.1 e (d+n))).mpr
    rw [sectionIdeal_on_any_frame k s hs v U (localPowerFrame U.1 e d),
      Ideal.mem_span_singleton]
    obtain ⟨b,hb⟩ := ho
    refine ⟨f^j*b,?_⟩
    change affineCoefficient U (localPowerFrame U.1 e (d+n)) t = f*(f^j*b)
    rw [hb]
    change f^(j+1)*b = _
    ring
  obtain ⟨q,hq,-⟩ := divide_by_power_section p L d n k s hs v hne t hv
  refine ⟨q,global_quotient_ne_zero _ t ht q hq,hq,?_⟩
  have he := affineCoefficient_division L U e d n (sectionCombination k s v) q
  rw [hq] at he
  have hd := he.dvd_iff_dvd_right.mpr ho
  change f^(j+1) ∣ f*affineCoefficient U (localPowerFrame U.1 e n) q at hd
  rw [pow_succ'] at hd
  exact (mul_dvd_mul_iff_left hf).mp hd

theorem power_multiple_order_bound (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)))
    (m : ℕ) : ∀ t : O X ⟶ (L.pow (d*m)).sheaf, t ≠ 0 →
      ¬ ((affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v))^(m+1) ∣
        affineCoefficient U (localPowerFrame U.1 e (d*m)) t) := by
  induction m with
  | zero =>
    intro t ht hd
    have sectionIsIso : IsIso t := proper_nonzero_structure_section_isIso p t ht
    have hu : IsUnit (affineCoefficient U (localPowerFrame U.1 e (d*0)) t) := by
      apply IsUnit.map U.1.topIso.hom.hom
      apply (end_isIso_iff _).mp
      dsimp only [coefficient,restrictSection]
      exact IsIso.comp_isIso'
        (IsIso.comp_isIso' (Scheme.Modules.restrictUnitIso U.1.ι).isIso_inv
          ((Scheme.Modules.restrictFunctor U.1.ι).map_isIso t))
        (localPowerFrame U.1 e (d*0)).isIso_hom
    simp only [Nat.mul_zero,Nat.zero_add,pow_one] at hd
    exact hnu (isUnit_of_dvd_unit hd hu)
  | succ m ih =>
    rw [Nat.mul_succ,Nat.add_comm (d*m) d]
    intro t ht hd
    obtain ⟨q,hq,he,ho⟩ := extract_power_with_order p L d (d*m) (m+1) k s hs v hne U e t ht hd
    exact ih q hq ho

theorem cartier_order_times_degree_le_power (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)))
    (a i : ℕ) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0)
    (ho : (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v))^i ∣
      affineCoefficient U (localPowerFrame U.1 e a) t) : i*d ≤ a := by
  let f := affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)
  let b := affineCoefficient U (localPowerFrame U.1 e a) t
  let E : ((L.pow a).pow d).sheaf ≅ (L.pow (d*a)).sheaf :=
    linePowerMul L a d ≪≫ eqToIso (congrArg (fun n => modulePow X L.sheaf n) (Nat.mul_comm a d))
  let q : O X ⟶ (L.pow (d*a)).sheaf := powerSection t d ≫ E.hom
  have ha := affineCoefficient_power (L.pow a) U (localPowerFrame U.1 e a) t d
    (localPowerFrame U.1 (localPowerFrame U.1 e a) d)
  have hb := affineCoefficient_iso U (localPowerFrame U.1 (localPowerFrame U.1 e a) d)
    (localPowerFrame U.1 e (d*a)) E (powerSection t d)
  have H : Associated (b^d) (affineCoefficient U (localPowerFrame U.1 e (d*a)) q) := ha.trans hb
  have hq : q ≠ 0 := by
    intro hq
    have hz : affineCoefficient U (localPowerFrame U.1 e (d*a)) q = 0 := by
      rw [hq]
      let frame : (L.pow (d*a)).sheaf.restrict U.1.ι ≅ O U.1.toScheme :=
        localPowerFrame U.1 e (d*a)
      exact (congrArg (fun value => U.1.topIso.hom value)
        ((congrArg (coefficient frame) (restrictSection_zero U.1.ι)).trans
          (coefficient_zero frame))).trans (map_zero U.1.topIso.hom.hom)
    have hn : b ≠ 0 := affineCoefficient_ne_zero (L.pow a) U _ t ht
    exact (pow_ne_zero d hn) (H.eq_zero_iff.mpr hz)
  by_contra hle
  have hlt : a+1 ≤ i*d := by omega
  have hd : f^(i*d) ∣ b^d := by
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd ho d
  have hdiv : f^(a+1) ∣ affineCoefficient U (localPowerFrame U.1 e (d*a)) q :=
    dvd_trans (pow_dvd_pow f hlt) (dvd_trans hd H.dvd)
  exact power_multiple_order_bound p L d k s hs v hne U e hnu a q hq hdiv

theorem small_power_restriction_ne_zero (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) {σ : Type} [Fintype σ]
    (k : ℂ →+* Γ(X,⊤)) (s : σ → (O X ⟶ (L.pow d).sheaf))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (v : σ → ℂ)
    (hne : sectionCombination k s v ≠ 0)
    [IsIntegral (sectionIdeal k s hs v).subscheme]
    (U : X.affineOpens) [Nonempty U.1]
    [Nonempty ((sectionIdeal k s hs v).subschemeι ⁻¹ᵁ U.1).toScheme]
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hnu : ¬ IsUnit (affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v)))
    (a : ℕ) (ha : a < d) (t : O X ⟶ (L.pow a).sheaf) (ht : t ≠ 0) :
    pullbackSection (sectionIdeal k s hs v).subschemeι t ≠ 0 := by
  intro hv
  have ho := (pullback_section_zero_iff_local_coefficient p _ (L.pow a) t U
    (localPowerFrame U.1 e a)).mp hv
  rw [sectionIdeal_on_any_frame k s hs v U (localPowerFrame U.1 e d),
    Ideal.mem_span_singleton] at ho
  change affineCoefficient U (localPowerFrame U.1 e d) (sectionCombination k s v) ∣
    affineCoefficient U (localPowerFrame U.1 e a) t at ho
  have hb := cartier_order_times_degree_le_power p L d k s hs v hne U e hnu a 1 t ht
    (by simpa only [pow_one] using ho)
  omega

end
end MaximalSeshadri.Geometry

end

end OAI
