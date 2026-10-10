import OAI.MeasureTheory.Falconer.Estimates.SourceProfileEquation25

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem sourceAngularH_two_profile_power {R : ℝ} (hR : 0 < R) (a v : ℝ) (Ψ : ℝ → ℝ)
    (U V : ℝ × UnitCircle → ℂ) (hU : Measurable U) (hV : Measurable V)
    {g₁ g₂ : ℝ} (hf₁ : sourceAngularH a v Ψ U U ≠ ⊤) (hf₂ : sourceAngularH a v Ψ V V ≠ ⊤)
    (hb₁ : (sourceAngularH a v Ψ U U).toReal ≤ R^g₁)
    (hb₂ : (sourceAngularH a v Ψ V V).toReal ≤ R^g₂) :
    sourceAngularH a v Ψ U V ≠ ⊤ ∧
      (sourceAngularH a v Ψ U V).toReal ≤ R^((g₁+g₂)/2) := by
  have hc := sourceAngularH_two_profile a v Ψ U V hU hV
  have hfinite : (sourceAngularH a v Ψ U U)^(1/2:ℝ)*(sourceAngularH a v Ψ V V)^(1/2:ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hf₁)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hf₂)
  refine ⟨ne_top_of_le_ne_top hfinite hc,?_⟩
  have hreal := ENNReal.toReal_mono hfinite hc
  rw [ENNReal.toReal_mul,← ENNReal.toReal_rpow,← ENNReal.toReal_rpow] at hreal
  calc
    _ ≤ (sourceAngularH a v Ψ U U).toReal^(1/2:ℝ)*
        (sourceAngularH a v Ψ V V).toReal^(1/2:ℝ) := hreal
    _ ≤ (R^g₁)^(1/2:ℝ)*(R^g₂)^(1/2:ℝ) := by gcongr
    _ = _ := by rw [← Real.rpow_mul hR.le,← Real.rpow_mul hR.le,← Real.rpow_add hR]; congr 1; ring

namespace RecursiveEnvironment

noncomputable def endpointTransform (e : RecursiveEnvironment) (c : ℕ) (X : CellPath)
    (k : PolicyDescriptor → ℕ) (h : Plane → ℂ) (z : ℝ × UnitCircle) : ℂ :=
  sourceAngularTransform e.ρ (e.Q.descendant X).carrier (((2:ℝ)^e.N)^(-e.mass c))
    (inheritedCircleSymbol ((e.angularData c e.N c e.N 0 X X).retainedList c) id k
      e.Q e.ρ e.mass e.N e.lam e.sig e.J 0 h) z.1 z.2

theorem endpointTransform_measurable (e : RecursiveEnvironment) [IsFiniteMeasure e.ρ] (c : ℕ) (X : CellPath)
    (k : PolicyDescriptor → ℕ) (h : Plane → ℂ) (hh : Measurable h) :
    Measurable (e.endpointTransform c X k h) :=
  measurable_sourceAngularTransform _ _ _ _ (measurable_inheritedCircleSymbol _ _ _ _ _ _ _ _ _ _ _ _ hh)

end RecursiveEnvironment

theorem uniform_two_profile_child_bound {lam sig kap eta : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1) (heta : 0 < eta) (K : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀, ∀ e : Fin 2 → RecursiveEnvironment,
      (∀ l, (e l).N = N) → (∀ l, (e l).lam = lam) → (∀ l, (e l).sig = sig) →
      (∀ l, (e l).q = sourcePolicyBlock N kap) → (∀ l, (e l).J = sourceSmoothingLevels sig kap) →
      (∀ l, (e l).Q.side = 1) → (∀ l, (e l).ρ (e l).Q.carrierᶜ = 0) →
      ∀ B : ℕ, ∀ δ : ℝ, (∀ l, RegularizedProfileData (e l).Q (e l).ρ N B δ lam (e l).mass) →
      ∀ c : ℕ, c+100*sourcePolicyBlock N kap < N →
      ∀ X : Fin 2 → CellPath, (∀ l, (X l).length = c) →
      ∀ k : Fin 2 → PolicyDescriptor → ℕ,
        (∀ l, ∑ b ∈ ((e l).angularData c N c N 0 (X l) (X l)).retainedList c, k l b ≤ K) →
      ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
      let U := (e 0).endpointTransform c (X 0) (k 0) (h 0)
      let V := (e 1).endpointTransform c (X 1) (k 1) (h 1)
      sourceAngularH c N Ψ U V ≠ ⊤ ∧
      (sourceAngularH c N Ψ U V).toReal ≤ ((2:ℝ)^N)^(
        (e 0).profile c+(e 1).profile c-
        (potential (e 0).profile c N (10*sourcePolicyBlock N kap)+
         potential (e 1).profile c N (10*sourcePolicyBlock N kap))/2+
        500*kap+10^6*(lam+sig)/kap+eta) := by
  obtain ⟨N₀,hN₀,h₀⟩ := source_profile_equation25 hlam hsig hkap hkap1 hgap hloss heta K hΨ hpos hs hone
  refine ⟨N₀,hN₀,?_⟩
  intro N hN e heN heLam heSig heq heJ heQ hecarry B δ hprof c hw X hX k hk h hh hhb
  let : ∀ l, IsProbabilityMeasure (e l).ρ := fun l => (hprof l).probability
  let g := fun l => 2*(e l).profile c-potential (e l).profile c N (10*sourcePolicyBlock N kap)
    +500*kap+10^6*(lam+sig)/kap+eta
  have hb (l : Fin 2) :
      sourceAngularH c N Ψ ((e l).endpointTransform c (X l) (k l) (h l))
        ((e l).endpointTransform c (X l) (k l) (h l)) ≠ ⊤ ∧
      (sourceAngularH c N Ψ ((e l).endpointTransform c (X l) (k l) (h l))
        ((e l).endpointTransform c (X l) (k l) (h l))).toReal ≤ ((2:ℝ)^N)^(g l) := by
    let d := (e l).angularData c N c N 0 (X l) (X l)
    have hdprof : RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass := by
      simpa only [d,RecursiveEnvironment.angularData,heN l,heLam l] using hprof l
    have hk' : ∀ j : Fin 2, ∑ b ∈ d.retainedList d.a, (fun _ : Fin 2 => k l) j b ≤ K := fun _ => hk l
    have hd := h₀ d (heLam l) (heSig l) (by simpa only [d,RecursiveEnvironment.angularData,heN l] using heq l)
      (heJ l) (by simpa only [d,RecursiveEnvironment.angularData,heN l] using hN)
      (heQ l) (hecarry l) rfl (by exact (heN l).symm) (by exact (heN l).symm) rfl
      (by simpa only [d,RecursiveEnvironment.angularData,heq l,heN l] using hw) (hX l) (hX l)
      B δ hdprof (fun _ => k l) hk' (fun _ => h l) (fun _ => hh l) (fun _ => hhb l)
    have henergy : d.energy (fun _ => k l) (fun _ => h l) Ψ =
        sourceAngularH c N Ψ ((e l).endpointTransform c (X l) (k l) (h l))
          ((e l).endpointTransform c (X l) (k l) (h l)) := by
      unfold AngularStateData.energy AngularStateData.cellEnergy
      congr 1 <;> funext z <;>
        simp only [RecursiveEnvironment.endpointTransform,d,RecursiveEnvironment.angularData,heN l]
    have hprofile : d.profile = (e l).profile := rfl
    change d.energy (fun _ => k l) (fun _ => h l) Ψ ≠ ⊤ ∧
      (d.energy (fun _ => k l) (fun _ => h l) Ψ).toReal ≤ ((2:ℝ)^d.N)^
        (2*d.profile c-potential d.profile c d.N (10*d.q)+500*kap+10^6*(lam+sig)/kap+eta) at hd
    rw [henergy,hprofile] at hd
    simpa only [d,RecursiveEnvironment.angularData,heN l,heq l,g] using hd
  have hr := sourceAngularH_two_profile_power (by positivity : 0 < (2:ℝ)^N) c N Ψ _ _
    ((e 0).endpointTransform_measurable c (X 0) (k 0) (h 0) (hh 0))
    ((e 1).endpointTransform_measurable c (X 1) (k 1) (h 1) (hh 1))
    (hb 0).1 (hb 1).1 (hb 0).2 (hb 1).2
  refine ⟨hr.1,hr.2.trans_eq ?_⟩
  congr 1
  dsimp only [g]
  ring

end PlanarFalconer

end OAI
