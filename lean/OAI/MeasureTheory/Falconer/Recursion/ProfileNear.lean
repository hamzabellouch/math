import OAI.MeasureTheory.Falconer.Estimates.RegularizedCellCounts
import OAI.MeasureTheory.Falconer.Graphs.NearGraph
import OAI.MeasureTheory.Falconer.Graphs.GraphNormalization
import OAI.MeasureTheory.Falconer.Angular.AngularTerminal

namespace OAI

/-! # The normalized near reduction for the actual regularized profile

The child energies retain the original endpoint symbols. No separation of
the parent cells is imposed; the near relation is on their two internal
center displacements, as in the manuscript.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}
attribute [local instance] Classical.propDecidable

noncomputable def profileModelMass (m : ℝ → ℝ) (N a : ℕ) : ℝ :=
  ((2:ℝ)^N)^(-m ((a:ℝ)/N))

theorem profile_near_prefactor {N : ℕ} (hN : 0 < N)
    (d : ℕ) (m : ℝ → ℝ) (a p : ℕ) (lam : ℝ) :
    (profileModelMass m N p/profileModelMass m N a)^4 *
      (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) *
      ((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) =
    ((2:ℝ)^N)^(-2*((m ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
      (m ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  have hr : (profileModelMass m N p/profileModelMass m N a)^4 =
      ((2:ℝ)^N)^(-4*(m ((p:ℝ)/N)-m ((a:ℝ)/N))) := by
    unfold profileModelMass
    rw [← Real.rpow_sub hR,← Real.rpow_natCast,← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [hr,← dyadic_rpow_change_base hN ((d:ℝ)*((p:ℝ)-a)),
    ← Real.rpow_add hR,← Real.rpow_add hR]
  congr 1
  ring

noncomputable def profileNearEnergy (Q₁ Q₂ : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N a p : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    (b c : Space d → Sphere d → ℂ) : ℝ :=
  (profileModelMass m N p/profileModelMass m N a)^4 *
    (2:ℝ)^((d:ℝ)*(v-a)) *
    ‖∫ z, ∑ row ∈ Q₁.occupiedPaths ρ (p-a) ×ˢ Q₂.occupiedPaths ρ (p-a),
      ∑ col ∈ Q₁.occupiedPaths ρ (p-a) ×ˢ Q₂.occupiedPaths ρ (p-a),
        if nearDyadicEdge Q₁ Q₂ (10*((d:ℝ)+1)/(2:ℝ)^p) row col then
          dyadicPairTransform Q₁ Q₂ ρ ρ (profileModelMass m N p)
            (profileModelMass m N p) b c row z *
          star (dyadicPairTransform Q₁ Q₂ ρ ρ (profileModelMass m N p)
            (profileModelMass m N p) b c col z) else 0
      ∂angularProductMeasure d v Ψ‖

theorem profile_near_reduction (Q : DyadicCube d) (hQ : Q.side = 1)
    (ρ : Measure (Space d)) {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    {a p : ℕ} (hap : a ≤ p) (hp : p ≤ N)
    (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (v : ℝ) (Ψ : ℝ → ℝ) [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C E : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    (hchild : ∀ row ∈ (Q.descendant X).occupiedPaths ρ (p-a) ×ˢ
        (Q.descendant Y).occupiedPaths ρ (p-a),
      independentAngularEnergy p v Ψ
        (fun z => endpointTransform
          (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
          (profileModelMass m N p) b z.1 z.2)
        (fun z => endpointTransform
          (ρ.restrict ((Q.descendant Y).descendant row.2).carrier)
          (profileModelMass m N p) c z.1 z.2) ≤ E) :
    profileNearEnergy (Q.descendant X) (Q.descendant Y) ρ m N a p v Ψ b c ≤
      ((2*(10*(d+1))+1)^(2*d):ℕ) *
      ((2:ℝ)^N)^(-2*((m ((p:ℝ)/N)-((d:ℝ)/2)*(p:ℝ)/N)-
        (m ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam)*E := by
  let := hreg.probability
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hside (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (Q.descendant Z).side = 1/(2:ℝ)^a := by rw [Q.descendant_side,hZ,hQ]
  have hgeom (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (10*((d:ℝ)+1)/(2:ℝ)^p)*((2:ℝ)^(p-a)/(Q.descendant Z).side) ≤
        (10*(d+1):ℕ) := by
    have he : (2:ℝ)^a*(2:ℝ)^(p-a) = (2:ℝ)^p := by
      rw [← pow_add,Nat.add_sub_of_le hap]
    rw [hside Z hZ]
    push_cast
    apply le_of_eq
    calc
      _ = 10*((d:ℝ)+1)*((2:ℝ)^a*(2:ℝ)^(p-a))/(2:ℝ)^p := by
        field_simp
      _ = _ := by rw [he]; field_simp
  have hM : 0 < profileModelMass m N p := by unfold profileModelMass; positivity
  have hn := dyadic_near_energy_bound (Q.descendant X) (Q.descendant Y)
    (Q.descendant_side_pos hQpos X) (Q.descendant_side_pos hQpos Y)
    ρ ρ (profileModelMass m N p) (profileModelMass m N p) hM hM b c hb hc
    hB hC hbB hcC (hgeom X hX) (hgeom Y hY) a p v Ψ
  have hs := Finset.sum_le_sum hchild
  rw [Finset.sum_const,nsmul_eq_mul] at hs
  have hrows := hreg.pair_count hap hp X Y hX hY
  have hsum := hs.trans (mul_le_mul_of_nonneg_right hrows hE)
  unfold profileNearEnergy
  rw [mul_assoc]
  apply (mul_le_mul_of_nonneg_left hn (by positivity)).trans
  calc
    _ = ((profileModelMass m N p/profileModelMass m N a)^4 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) * ((2*(10*(d+1))+1)^(2*d):ℕ)) *
        ∑ row ∈ (Q.descendant X).occupiedPaths ρ (p-a) ×ˢ
          (Q.descendant Y).occupiedPaths ρ (p-a),
          independentAngularEnergy p v Ψ
            (fun z => endpointTransform
              (ρ.restrict ((Q.descendant X).descendant row.1).carrier)
              (profileModelMass m N p) b z.1 z.2)
            (fun z => endpointTransform
              (ρ.restrict ((Q.descendant Y).descendant row.2).carrier)
              (profileModelMass m N p) c z.1 z.2) := by ring
    _ ≤ ((profileModelMass m N p/profileModelMass m N a)^4 *
        (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) * ((2*(10*(d+1))+1)^(2*d):ℕ)) *
        (((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam)*E) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((2*(10*(d+1))+1)^(2*d):ℕ) *
        ((profileModelMass m N p/profileModelMass m N a)^4 *
          (2:ℝ)^((d:ℝ)*((p:ℝ)-a)) *
          ((2:ℝ)^N)^(2*(m ((p:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam))*E := by ring
    _ = _ := by rw [profile_near_prefactor hN]

theorem profile_angular_terminal (Q : DyadicCube d) (ρ : Measure (Space d))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m) (hN : 0 < N)
    {a q : ℕ} (ha : a ≤ N) (X Y : List (Fin d → Bool))
    (hX : X.length = a) (hY : Y.length = a) (v : ℝ)
    (hv : v ≤ (a:ℝ)+100*q) (Ψ : ℝ → ℝ) {W B : ℝ}
    (hW : 0 ≤ W) (hΨ : ∀ t, Ψ t ≤ W) (hsupp : ∀ t, 4 < t → Ψ t = 0)
    (hB : 0 ≤ B) (b c : Space d → Sphere d → ℂ)
    (hb : ∀ x w, ‖b x w‖ ≤ B) (hc : ∀ x w, ‖c x w‖ ≤ B) :
    independentAngularEnergy a v Ψ
      (fun z => endpointTransform (ρ.restrict (Q.descendant X).carrier)
        (profileModelMass m N a) b z.1 z.2)
      (fun z => endpointTransform (ρ.restrict (Q.descendant Y).carrier)
        (profileModelMass m N a) c z.1 z.2) ≤
    (4*W*B^4*(sphereMeasure d).real univ^2) *
      ((2:ℝ)^N)^(100*(d:ℝ)*q/N+4*((d:ℝ)+1)*lam) := by
  let := hreg.probability
  have hR : 0 < (2:ℝ)^N := by positivity
  have hM : 0 < profileModelMass m N a := by unfold profileModelMass; positivity
  have hm (Z : List (Fin d → Bool)) (hZ : Z.length = a) :
      (ρ.restrict (Q.descendant Z).carrier).real univ/profileModelMass m N a ≤
        ((2:ℝ)^N)^(((d:ℝ)+1)*lam) := by
    rw [measureReal_def,Measure.restrict_apply_univ]
    apply (div_le_iff₀ hM).mpr
    exact (hreg.cell_mass_upper ha Z hZ).trans_eq
      (by rw [profileModelMass,← Real.rpow_add hR]; rfl)
  have h := endpoint_angular_terminal (a:ℝ) v Ψ hW hΨ hsupp hB hR
    (ρ.restrict (Q.descendant X).carrier) (ρ.restrict (Q.descendant Y).carrier)
    (profileModelMass m N a) (profileModelMass m N a) hM hM
    (hm X hX) (hm Y hY) b c hb hc
  have hwidth : (2:ℝ)^((d:ℝ)*(v-a)) ≤
      ((2:ℝ)^N)^(100*(d:ℝ)*q/N) := by
    rw [dyadic_rpow_change_base hN]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  apply h.trans
  calc
    _ ≤ (4*W*B^4*(sphereMeasure d).real univ^2) *
        ((2:ℝ)^N)^(100*(d:ℝ)*q/N) * ((2:ℝ)^N)^(4*(((d:ℝ)+1)*lam)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth (by positivity))
        (by positivity)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hR]; congr 2; ring

end Falconer

end OAI
