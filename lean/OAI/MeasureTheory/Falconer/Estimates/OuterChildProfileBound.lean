import OAI.MeasureTheory.Falconer.Recursion.OuterRecursiveTransport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

noncomputable def outerChildEnergy (Q : Fin 2 → DyadicSquare)
    (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (N q c J : ℕ)
    (lam sig : ℝ) (k : Fin 2 → PolicyDescriptor → ℕ)
    (h : Fin 2 → Plane → ℂ) (Ψ : ℝ → ℝ) (row : CellPath × CellPath) : ℝ≥0∞ :=
  sourceAngularH c N Ψ
    (fun z => sourceAngularTransform (ρ 0) ((Q 0).descendant row.1).carrier
      (((2:ℝ)^N)^(-mass 0 c))
      (inheritedCircleSymbol (outerDescriptorList (mass 0) N q c) id (k 0)
        (Q 0) (ρ 0) (mass 0) N lam sig J 0 (h 0)) z.1 z.2)
    (fun z => sourceAngularTransform (ρ 1) ((Q 1).descendant row.2).carrier
      (((2:ℝ)^N)^(-mass 1 c))
      (inheritedCircleSymbol (outerDescriptorList (mass 1) N q c) id (k 1)
        (Q 1) (ρ 1) (mass 1) N lam sig J 0 (h 1)) z.1 z.2)

theorem uniform_outer_child_profile_bound {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1) (heta : 0 < eta) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ),
      (∀ l, (Q l).side = 1) → (∀ l, ρ l (Q l).carrierᶜ = 0) →
      ∀ B : ℕ, ∀ δ : ℝ, (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
      ∀ c : ℕ, c+100*sourcePolicyBlock N kap < N →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ,
        (∀ l, ∑ b ∈ outerDescriptorList (mass l) N (sourcePolicyBlock N kap) c, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      let A := fun l (n : ℕ) => mass l n-(n:ℝ)/N
      let E := outerChildEnergy Q ρ mass N (sourcePolicyBlock N kap) c
        (sourceSmoothingLevels sig kap) lam sig k h Ψ
      let bound := ((2:ℝ)^N)^(A 0 c+A 1 c-
        (potential (A 0) c N (10*sourcePolicyBlock N kap)+
         potential (A 1) c N (10*sourcePolicyBlock N kap))/2+
        500*kap+10^6*(lam+sig)/kap+eta)
      (∀ row : CellPath × CellPath, row.1.length = c → row.2.length = c →
        E row ≠ ⊤ ∧ (E row).toReal ≤ bound) ∧
      (∀ S : Finset (CellPath × CellPath),
        (∀ row ∈ S, row.1.length = c ∧ row.2.length = c) →
        finiteEnergyMaximum S E ≤ bound) := by
  classical
  obtain ⟨N₁,hN₁,h₁⟩ := uniform_two_profile_child_bound hlam hsig hkap hkap1 hgap hloss
    (half_pos heta) K hΨ hpos hs hone
  obtain ⟨N₂,h₂⟩ := fixed_constant_absorbed (half_pos heta) ((symbolDerivativeConstant K^K)^4)
  refine ⟨max N₁ N₂,lt_of_lt_of_le hN₁ (le_max_left _ _),?_⟩
  intro N hN Q ρ mass hQ hcarry B δ hprof c hw k hk h hh hhb
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hprof l).probability
  let q := sourcePolicyBlock N kap
  let J := sourceSmoothingLevels sig kap
  let e : Fin 2 → RecursiveEnvironment := fun l => ⟨Q l,ρ l,mass l,N,q,J,lam,sig⟩
  have hQpos (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  dsimp only
  have hb (row : CellPath × CellPath) (hX : row.1.length = c) (hY : row.2.length = c) :
      outerChildEnergy Q ρ mass N q c J lam sig k h Ψ row ≠ ⊤ ∧
      (outerChildEnergy Q ρ mass N q c J lam sig k h Ψ row).toReal ≤
        ((2:ℝ)^N)^((e 0).profile c+(e 1).profile c-
          (potential (e 0).profile c N (10*q)+potential (e 1).profile c N (10*q))/2+
          500*kap+10^6*(lam+sig)/kap+eta) := by
    have hf := inherited_product_energy_finite (fun l => outerDescriptorList (mass l) N q c)
      (fun _ => id) k K hk Q hQpos ρ mass N lam sig J 0 h hh hhb
      ((Q 0).descendant row.1).carrier ((Q 1).descendant row.2).carrier c N
      (by positivity : 0 < ((2:ℝ)^N)^(-mass 0 c))
      (by positivity : 0 < ((2:ℝ)^N)^(-mass 1 c)) hΨ hpos hs
    refine ⟨hf,?_⟩
    let X : Fin 2 → CellPath := ![row.1,row.2]
    have hdepth (l : Fin 2) : (X l).length = c := by fin_cases l <;> assumption
    have hk' (l : Fin 2) :
        ∑ b ∈ ((e l).angularData c N c N 0 (X l) (X l)).retainedList c, k l b ≤ K :=
      outer_remaining_budget (mass l) N q c K (k l) (hk l)
    have hbase := h₁ N ((le_max_left _ _).trans hN) e (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hQ hcarry B δ hprof c hw X hdepth k hk' h hh hhb
    have hdrop := inherited_product_energy_drop_real (fun l => outerDescriptorList (mass l) N q c)
      (fun _ => id) k K hk Q hQpos ρ mass N lam sig J 0 h hh hhb row c N
      (by positivity : 0 < ((2:ℝ)^N)^(-mass 0 c))
      (by positivity : 0 < ((2:ℝ)^N)^(-mass 1 c)) hΨ hpos hs
    dsimp only at hdrop
    rw [outer_remaining_energy Q ρ mass N q c J lam sig k h Ψ row hX hY] at hdrop
    let g := (e 0).profile c+(e 1).profile c-
      (potential (e 0).profile c N (10*q)+potential (e 1).profile c N (10*q))/2+
      500*kap+10^6*(lam+sig)/kap
    calc
      _ ≤ (symbolDerivativeConstant K^K)^4 *
          (sourceAngularH c N Ψ ((e 0).endpointTransform c row.1 (k 0) (h 0))
            ((e 1).endpointTransform c row.2 (k 1) (h 1))).toReal := hdrop.2
      _ ≤ (symbolDerivativeConstant K^K)^4 * ((2:ℝ)^N)^(g+eta/2) :=
        mul_le_mul_of_nonneg_left hbase.2 (by positivity)
      _ ≤ ((2:ℝ)^N)^(eta/2) * ((2:ℝ)^N)^(g+eta/2) :=
        mul_le_mul_of_nonneg_right (h₂ N ((le_max_right _ _).trans hN)) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; dsimp only [g]; ring
  refine ⟨hb,?_⟩
  intro S hS
  apply finiteEnergyMaximum_le S _ (by positivity)
  intro row hr
  exact (hb row (hS row hr).1 (hS row hr).2).2

end PlanarFalconer

end OAI
