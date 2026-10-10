import Mathlib
import OAI.Geometry.NearbyLagrangian.PhaseConjugacy

namespace OAI

/-! Finite composition and complete tame Hamiltonian transport. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport
open ContinuousLinearMap Set Filter
open scoped ContDiff Topology InnerProductSpace
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def preparedComposite {S : Set (E × E)} {δ : ℝ} :
    (n : ℕ) → (Fin n → PreparedMixedStep S δ) → E × E → E × E
  | 0, _, z => z
  | n+1, steps, z => (steps (Fin.last n)).ψ
      (preparedComposite n (fun i => steps i.castSucc) z)

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

theorem finite_tame_transport {S : Set (E × E)} {δ : ℝ}
    (hS : IsCompact S) {U : Set E} (hU : IsOpen U)
    (hSU : ∀ z ∈ S, z.1 ∈ U) (hδ : 0 < δ)
    {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ)
    (hζr : ∀ x, ζ x ∈ Icc (0:ℝ) 1)
    (hζ1 : ∀ x ∈ Prod.fst '' S, ζ =ᶠ[𝓝 x] fun _ => 1)
    (hbuf : ∀ x ∈ tsupport ζ, ∀ v, ‖v‖ ≤ 2*δ → x+v ∈ U)
    {F g : E × W → ℝ} (T : TameOn U F g) (hM : MorseOn U F) :
    ∀ (n : ℕ) (steps : Fin n → PreparedMixedStep S δ),
      ∃ F' : E × TransportFiber E W n → ℝ,
        TameOn U F' (iterReference g n) ∧ MorseOn U F' ∧
        ∃ e : PhaseCritical U F ≃ₜ PhaseCritical U F',
          ∀ q, phaseGenerate F' (e q).val =
            preparedComposite n steps (phaseGenerate F q.val) := by
  intro n
  induction n with
  | zero =>
    intro steps
    exact ⟨F,T,hM,Homeomorph.refl _,fun _ => rfl⟩
  | succ n ih =>
    intro steps
    obtain ⟨Fn,Tn,Mn,en,hn⟩ := ih (fun i => steps i.castSucc)
    obtain ⟨Fn',Tn',Mn',en',hn'⟩ := (steps (Fin.last n)).tame_step
      hS hU hSU hδ hζ hζc hζr hζ1 hbuf Tn Mn
    refine ⟨Fn',Tn',Mn',en.trans en',?_⟩
    intro q
    change phaseGenerate Fn' (en' (en q)).val =
      (steps (Fin.last n)).ψ (preparedComposite n (fun i => steps i.castSucc) (phaseGenerate F q.val))
    rw [hn',hn]

omit [FiniteDimensional ℝ W] in

theorem phaseGenerate_injective_of_conjugacy {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {U : Set E} {F : E × W → ℝ} {G : E × V → ℝ}
    (e : PhaseCritical U F ≃ₜ PhaseCritical U G) {ψ : E × E → E × E}
    (hψ : Function.Injective ψ)
    (he : ∀ q, phaseGenerate G (e q).val = ψ (phaseGenerate F q.val))
    (hF : Function.Injective (fun q : PhaseCritical U F => phaseGenerate F q.val)) :
    Function.Injective (fun q : PhaseCritical U G => phaseGenerate G q.val) := by
  intro x y hxy
  obtain ⟨a,rfl⟩ := e.surjective x
  obtain ⟨b,rfl⟩ := e.surjective y
  change phaseGenerate G (e a).val = phaseGenerate G (e b).val at hxy
  rw [he,he] at hxy
  exact congrArg e (hF (hψ hxy))

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Filter ContinuousLinearMap InnerProductSpace SmoothFlow
open scoped ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma flat_hamiltonian_evolution_endpoint {H : ℝ × (E × E) → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Icc (0:ℝ) 1 ×ˢ univ))
    (φ : ODE.CompleteFlow (timeLift (hamiltonianField (flatTimeField H))))
    {K : ℝ≥0} (hK : LipschitzWith K (hamiltonianField (flatTimeField H))) {y : ℝ → E × E}
    (hy : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivWithinAt y (hamiltonianField H (t,y t)) (Icc (0:ℝ) 1) t) :
    evolution φ ((0,y 0),1) = y 1 := by
  have hd (t : ℝ) : HasDerivAt (fun u => y (Real.smoothTransition u))
      (hamiltonianField (flatTimeField H) (t,y (Real.smoothTransition t))) t := by
    rw [flatHamiltonian_field hH]
    exact flatTime_solution hy t
  have he := evolution_unique φ hK hd
    (show y (Real.smoothTransition (0:ℝ)) = y 0 by simp) 1
  simpa only [Real.smoothTransition.one_of_one_le le_rfl] using he

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open ContinuousLinearMap Set Filter SmoothFlow
open scoped ContDiff Topology InnerProductSpace NNReal
variable {E W : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
lemma preparedComposite_evolution {X : ℝ × (E × E) → E × E}
    (φ : ODE.CompleteFlow (timeLift X)) {K : ℝ≥0} (hK : LipschitzWith K X)
    (times : ℕ → ℝ) {S : Set (E × E)} {δ : ℝ} :
    ∀ (n : ℕ) (steps : Fin n → PreparedMixedStep S δ),
      (∀ i z, (steps i).ψ z = evolution φ ((times i.val,z),times (i.val+1))) →
      ∀ z, preparedComposite n steps z = evolution φ ((times 0,z),times n) := by
  intro n
  induction n with
  | zero =>
    intro steps _ z
    exact (evolution_initial φ (times 0) z).symm
  | succ n ih =>
    intro steps hstep z
    change (steps (Fin.last n)).ψ (preparedComposite n (fun i => steps i.castSucc) z) = _
    rw [ih (fun i => steps i.castSucc) (fun i z => hstep i.castSucc z),hstep]
    exact evolution_cocycle φ hK (times 0) (times n) (times (n+1)) z

theorem tame_hamiltonian_transport {U : Set E} (hU : IsOpen U)
    {S : Set (E × E)} (hS : IsCompact S) (hSU : ∀ z ∈ S, z.1 ∈ U)
    {H : ℝ × (E × E) → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Icc (0:ℝ) 1 ×ˢ univ))
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => H (t,x)) ⊆ S)
    {F g : E × W → ℝ} (T : TameOn U F g) (hM : MorseOn U F) :
    ∃ (n : ℕ) (F' : E × TransportFiber E W n → ℝ) (K : ℝ≥0)
      (φ : ODE.CompleteFlow (timeLift (hamiltonianField (flatTimeField H)))),
      0 < n ∧ LipschitzWith K (hamiltonianField (flatTimeField H)) ∧
      TameOn U F' (iterReference g n) ∧ MorseOn U F' ∧
      ∃ e : PhaseCritical U F ≃ₜ PhaseCritical U F',
        ∀ q, phaseGenerate F' (e q).val = evolution φ ((0,phaseGenerate F q.val),1) := by
  obtain ⟨ζ,δ,n,K,φ,steps,hζ,hζc,hζr,hζ1,hδ,hn,hbuf,hK,hsteps⟩ :=
    exists_finite_prepared_steps hU hS hSU hH hs
  obtain ⟨F',T',M',e,he⟩ := finite_tame_transport hS hU hSU hδ hζ hζc hζr hζ1 hbuf T hM n steps
  refine ⟨n,F',K,φ,hn,hK,T',M',e,fun q => ?_⟩
  rw [he,preparedComposite_evolution φ hK (fun j => (j:ℝ)/n) n steps hsteps]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Nat.cast_zero,zero_div,div_self hn']

theorem tame_hamiltonian_transport_endpoint {U : Set E} (hU : IsOpen U)
    {S : Set (E × E)} (hS : IsCompact S) (hSU : ∀ z ∈ S, z.1 ∈ U)
    {H : ℝ × (E × E) → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Icc (0:ℝ) 1 ×ˢ univ))
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => H (t,x)) ⊆ S)
    {F g : E × W → ℝ} (T : TameOn U F g) (hM : MorseOn U F) :
    ∃ (n : ℕ) (F' : E × TransportFiber E W n → ℝ),
      TameOn U F' (iterReference g n) ∧ MorseOn U F' ∧
      ∃ e : PhaseCritical U F ≃ₜ PhaseCritical U F',
        ∀ (q : PhaseCritical U F) (y : ℝ → E × E),
          (∀ t ∈ Icc (0:ℝ) 1,
            HasDerivWithinAt y (hamiltonianField H (t,y t)) (Icc (0:ℝ) 1) t) →
          y 0 = phaseGenerate F q.val → phaseGenerate F' (e q).val = y 1 := by
  obtain ⟨n,F',K,φ,_hn,hK,T',M',e,he⟩ := tame_hamiltonian_transport hU hS hSU hH hs T hM
  refine ⟨n,F',T',M',e,?_⟩
  intro q y hy hy0
  rw [he,← hy0]
  exact flat_hamiltonian_evolution_endpoint hH φ hK hy

end NearbyLagrangian.Transport

end

end OAI
