import OAI.MeasureTheory.Falconer.Graphs.ActualProductChildEnergy
import OAI.MeasureTheory.Falconer.Graphs.ProductEnergyMaximum

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem uniform_actual_product_estimate
    {sig c₀ : ℝ} (hsig : 0 < sig) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi)
    (K : ℕ) (lam T : ℝ) (hlam : 0 ≤ lam) {η : ℝ} (hη : 0 < η) {J : ℕ} (hJ : 0 < J) {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ t, 0 ≤ Ψ t) (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (i : ℕ) (h : Fin 2 → Plane → ℂ), i < J → (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N →
    0 ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ e ∈ S 0, ∀ g : ℕ, d 0 e = .parallel g (a+n) →
    a ≤ g → g ≤ a+n → (g:ℝ)-a ≤ 2*sig*N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let U := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 0) X.carrier
      (((2:ℝ)^N)^(-mass 0 a)) (β 0) z.1 z.2
    let V := fun z : ℝ × UnitCircle => sourceAngularTransform (ρ 1) Y.carrier
      (((2:ℝ)^N)^(-mass 1 a)) (β 1) z.1 z.2
    let Uc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 0) ((Q 0).descendant P).carrier (M 0) (β 0) z.1 z.2
    let Vc := fun P : CellPath => fun z : ℝ × UnitCircle =>
      sourceAngularTransform (ρ 1) ((Q 1).descendant P).carrier (M 1) (β 1) z.1 z.2
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
    (sourceAngularH a v Ψ U V).toReal ≤
      ((2:ℝ)^N)^(
        -(mass 0 (a+n)-((a:ℝ)+n)/N-(mass 0 a-(a:ℝ)/N))
        -(mass 1 (a+n)-((a:ℝ)+n)/N-(mass 1 a-(a:ℝ)/N))
        +height (fun t : ℕ => mass 0 t-(t:ℝ)/(N:ℝ)) a (a+n)+4000*(lam+sig)+η) *
      finiteEnergyMaximum (sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B n)
        (fun row => sourceAngularH (a+n) v Ψ (Uc row.1) (Vc row.2)) + ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₁,hchild⟩ := uniform_actual_product_H_child_sum hsig hc hcap K lam T hJ hΨ hpos hs
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hη (589824:ℝ)
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hu ht hLu hv
    e he g hdesc hag hgp hgap A B' hA hB
  have hNpos : 0 < N := (by omega : 0 < max 1 (max N₁ N₂)).trans_le hN
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hg := hchild N hN₁ S d k hcard hK L hL Q hQ ρ mass B δ hd i h hi hh hhb a n v hp hu ht hLu hv
    e he g hdesc hag hgp hgap A B' hA hB
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  let E := fun row : CellPath × CellPath => sourceAngularH ((a:ℝ)+n) v Ψ
    (fun z => sourceAngularTransform (ρ 0) ((Q 0).descendant row.1).carrier
      (((2:ℝ)^N)^(-mass 0 (a+n))) (β 0) z.1 z.2)
    (fun z => sourceAngularTransform (ρ 1) ((Q 1).descendant row.2).carrier
      (((2:ℝ)^N)^(-mass 1 (a+n))) (β 1) z.1 z.2)
  let C := sourceProductVertices (Q 0) (Q 1) (ρ 0) (ρ 1) A B' n
  let k0 := height (fun t : ℕ => mass 0 t-(t:ℝ)/(N:ℝ)) a (a+n)
  have hcount := sourceProductVertices_profile_count (Q 0) (Q 1) (hQ 0) (hQ 1)
    (ρ 0) (ρ 1) N B δ lam (mass 0) (mass 1) (hd 0) (hd 1) A B' a n hA hB hp
  have hmax := product_profile_sum_bound C E N hNpos (mass 0) (mass 1) a ((a:ℝ)+n)
    (k0+2000*(lam+sig)+64*sig) lam hcount
  let x := -(mass 0 (a+n)-((a:ℝ)+n)/N-(mass 0 a-(a:ℝ)/N))
    -(mass 1 (a+n)-((a:ℝ)+n)/N-(mass 1 a-(a:ℝ)/N))
  have hpower : 589824*((2:ℝ)^N)^(x+(k0+2000*(lam+sig)+64*sig)+12*lam) ≤
      ((2:ℝ)^N)^(x+k0+4000*(lam+sig)+η) := by
    calc
      _ ≤ ((2:ℝ)^N)^η*((2:ℝ)^N)^(x+(k0+2000*(lam+sig)+64*sig)+12*lam) :=
        mul_le_mul_of_nonneg_right (hconst N hN₂) (by positivity)
      _ = ((2:ℝ)^N)^(η+(x+(k0+2000*(lam+sig)+64*sig)+12*lam)) :=
        (Real.rpow_add (by positivity : (0:ℝ)<(2:ℝ)^N) _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)
  have hmax' := hmax.trans (mul_le_mul_of_nonneg_right hpower (finiteEnergyMaximum_nonneg C E))
  dsimp only at hg ⊢
  refine ⟨hg.1,?_⟩
  apply hg.2.trans
  simpa only [C,E,β,k0,x] using add_le_add hmax' (le_refl (((2:ℝ)^N)^(-T)))

end PlanarFalconer

end OAI
