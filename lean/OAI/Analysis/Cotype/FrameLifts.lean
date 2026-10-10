import OAI.Analysis.Cotype.EquivariantPairing

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {n m : ℕ}

@[instance_reducible] def primalTupleAction : MulAction (WalshSymmetry n) (Fin m → Cube n) where
  smul g U := fun i => primalSymmetry g (U i)
  one_smul U := by funext i; rfl
  mul_smul g h U := by funext i; rfl

@[instance_reducible] def dualTupleAction : MulAction (WalshSymmetry n) (Fin m → Cube n) where
  smul g U := fun i => dualSymmetry g (U i)
  one_smul U := by funext i; rfl
  mul_smul g h U := by funext i; rfl

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem exists_primal_tuple_lifts [CompleteSpace X] (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (SymmetryL2 n X →L[ℝ] ℝ) m D) (hDone : 1 ≤ D)
    (x : Cube n → SymmetryL2 n X) (hx : ∀ u, ‖x u‖ ≤ 1)
    (he : ∀ g u, rightTranslation g (x u) = x (primalSymmetry g u)) :
    ∃ P : (Fin m → Cube n) → Cube m → SymmetryL2 n X,
      (∀ U ε, ‖P U ε‖ ≤ 1) ∧
      (∀ U i, moment (SymmetryL2 n X) (P U) i = (1/(2*24*D*Real.sqrt m)) • x (U i)) ∧
      ∀ g U ε, P (fun i => primalSymmetry g (U i)) ε = rightTranslation g (P U ε) := by
  let := primalTupleAction (n := n) (m := m)
  exact exists_equivariant_primal_lifts (Γ := WalshSymmetry n) (I := Fin m → Cube n)
    (X := SymmetryL2 n X) hm hD hDone rightTranslation
    (fun U i => x (U i)) (fun U i => hx (U i)) (fun g U i => (he g (U i)).symm)

theorem exists_dual_tuple_lifts (hm : 0 < m) {D : ℝ}
    (hD : FixedCotypeBound (SymmetryL2 n Y) m D) (hDone : 1 ≤ D)
    (y : Cube n → (SymmetryL2 n Y →L[ℝ] ℝ)) (hy : ∀ v, ‖y v‖ ≤ 1)
    (he : ∀ g v, dualAction (rightTranslation (X := Y)) g (y v) = y (dualSymmetry g v)) :
    ∃ Z : (Fin m → Cube n) → Cube m → (SymmetryL2 n Y →L[ℝ] ℝ),
      (∀ V δ, ‖Z V δ‖ ≤ 1) ∧
      (∀ V i, moment (SymmetryL2 n Y →L[ℝ] ℝ) (Z V) i = (1/(2*24*D*Real.sqrt m)) • y (V i)) ∧
      ∀ g V δ, Z (fun i => dualSymmetry g (V i)) δ =
        dualAction (rightTranslation (X := Y)) g (Z V δ) := by
  let := dualTupleAction (n := n) (m := m)
  exact exists_equivariant_dual_lifts (Γ := WalshSymmetry n) (I := Fin m → Cube n)
    (Y := SymmetryL2 n Y) hm hD hDone (dualAction rightTranslation)
    (fun V i => y (V i)) (fun V i => hy (V i)) (fun g V i => (he g (V i)).symm)

abbrev GrowthSpace (n : ℕ) (X : Type*) : Type _ := SymmetryL2 n (PiLp 2 (fun _ : Cube (n+n) => X))

structure GrowthPairingData (T : X →L[ℝ] Y) (n m : ℕ) (Dg Df : ℝ) where
  gamma : ℝ
  gamma_half : walshNorm n T / 2 < gamma
  gamma_pos : 0 < gamma
  x : Cube n → GrowthSpace n X
  y : Cube n → (GrowthSpace n Y →L[ℝ] ℝ)
  P : (Fin m → Cube n) → Cube m → GrowthSpace n X
  Z : (Fin m → Cube n) → Cube m → (GrowthSpace n Y →L[ℝ] ℝ)
  x_norm : ∀ u, ‖x u‖ ≤ 1
  y_norm : ∀ v, ‖y v‖ ≤ 1
  P_norm : ∀ U ε, ‖P U ε‖ ≤ 1
  Z_norm : ∀ V δ, ‖Z V δ‖ ≤ 1
  exact_pairing : ∀ u v, y v (l2Amplification (l2Amplification T) (x u)) = gamma * character v u
  P_moment : ∀ U i, moment (GrowthSpace n X) (P U) i = (1/(2*24*Dg*Real.sqrt m)) • x (U i)
  Z_moment : ∀ V i, moment (GrowthSpace n Y →L[ℝ] ℝ) (Z V) i = (1/(2*24*Df*Real.sqrt m)) • y (V i)
  x_equivariant : ∀ g u, rightTranslation g (x u) = x (primalSymmetry g u)
  y_equivariant : ∀ g v, dualAction (rightTranslation (X := PiLp 2 (fun _ : Cube (n+n) => Y))) g (y v) = y (dualSymmetry g v)
  P_equivariant : ∀ g U ε, P (fun i => primalSymmetry g (U i)) ε = rightTranslation g (P U ε)
  Z_equivariant : ∀ g V δ, Z (fun i => dualSymmetry g (V i)) δ =
    dualAction (rightTranslation (X := PiLp 2 (fun _ : Cube (n+n) => Y))) g (Z V δ)
  walsh_norms : ∀ k, walshNorm k (l2Amplification (Ω := WalshSymmetry n)
    (l2Amplification (Ω := Cube (n+n)) T)) = walshNorm k T

theorem exists_growthPairingData [CompleteSpace X] (n : ℕ) (hm : 0 < m)
    {Dg Df : ℝ} (hDg : FixedCotypeBound (X →L[ℝ] ℝ) m Dg)
    (hDf : FixedCotypeBound Y m Df) (hDg1 : 1 ≤ Dg) (hDf1 : 1 ≤ Df)
    {T : X →L[ℝ] Y} (hT : T ≠ 0) : Nonempty (GrowthPairingData T n m Dg Df) := by
  obtain ⟨γ,x,y,hγ,hγp,hx,hy,hxy,hxe,hye,hW⟩ := exists_equivariant_exact_pairing n hT
  have hG := fixedCotypeBound_dual_l2Amplification (Ω := WalshSymmetry n)
    (fixedCotypeBound_dual_l2Amplification (Ω := Cube (n+n)) hDg)
  have hF := fixedCotypeBound_l2Amplification (Ω := WalshSymmetry n)
    (fixedCotypeBound_l2Amplification (Ω := Cube (n+n)) hDf)
  obtain ⟨P,hPn,hPm,hPe⟩ := exists_primal_tuple_lifts hm hG hDg1 x hx hxe
  obtain ⟨Z,hZn,hZm,hZe⟩ := exists_dual_tuple_lifts hm hF hDf1 y hy hye
  exact ⟨⟨γ,hγ,hγp,x,y,P,Z,hx,hy,hPn,hZn,hxy,hPm,hZm,hxe,hye,hPe,hZe,hW⟩⟩

end Cotype

end

end OAI
