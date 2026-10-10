import OAI.Dynamics.EntropyCounterexample.CylinderModels
import OAI.Dynamics.EntropyCounterexample.EntropyLocalization

namespace OAI

noncomputable section

open Filter Topology

namespace Problem340

theorem entropy_zero_of_counterexample_orbit_data
    (q : ℕ) (F : CounterexampleManifold q → CounterexampleManifold q)
    (hF : Continuous F)
    (clock₀ : StandardClock) (sphere₀ sphereInf : StandardSphere2)
    (R : StandardSphere2 → StandardSphere2) (g : StandardClock → StandardClock)
    (hzeroInv : Set.MapsTo F (clockMainCylinder clock₀ sphere₀ 0)
      (clockMainCylinder clock₀ sphere₀ 0))
    (hInfInv : Set.MapsTo F
      (sphereVectorCylinder (Function.update (fun _ : Fin (q + 1) => sphere₀) 0 sphereInf))
      (sphereVectorCylinder (Function.update (fun _ : Fin (q + 1) => sphere₀) 0 sphereInf)))
    (hR : ∀ p ∈ clockMainCylinder clock₀ sphere₀ (0 : Fin (q + 1)),
      ∀ k : Fin q, (F p).2 k.succ = R (p.2 k.succ))
    (hg : ∀ p ∈ sphereVectorCylinder
      (Function.update (fun _ : Fin (q + 1) => sphere₀) 0 sphereInf),
      (F p).1 = g p.1)
    (hREntropy : Dynamics.coverEntropy
      (fun v : Fin q → StandardSphere2 => fun k => R (v k)) Set.univ = 0)
    (hgEntropy : Dynamics.coverEntropy g Set.univ = 0)
    (horbit : ∀ x : CounterexampleManifold q,
      (Tendsto (fun n => (F^[n] x).1) atTop (𝓝 clock₀) ∧
        Tendsto (fun n => (F^[n] x).2 0) atTop (𝓝 sphere₀)) ∨
      (Tendsto (fun n => (F^[n] x).2 0) atTop (𝓝 sphereInf) ∧
        ∀ k : Fin (q + 1), k ≠ 0 → ∀ᶠ n in atTop, (F^[n] x).2 k = sphere₀)) :
    Dynamics.coverEntropy F (Set.univ : Set (CounterexampleManifold q)) = 0 := by
  let vInf : Fin (q + 1) → StandardSphere2 :=
    Function.update (fun _ => sphere₀) 0 sphereInf
  let K : Set (CounterexampleManifold q) :=
    clockMainCylinder clock₀ sphere₀ 0 ∪ sphereVectorCylinder vInf
  have hK : IsCompact K :=
    counterexample_attractor_isCompact q clock₀ sphere₀ sphereInf 0
  have hKne : K.Nonempty :=
    (clockMainCylinder_nonempty clock₀ sphere₀ (0 : Fin (q + 1))).mono Set.subset_union_left
  have hKInv : Set.MapsTo F K K := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hzeroInv hx)
    · exact Or.inr (hInfInv hx)
  have hKEntropy : Dynamics.coverEntropy F K = 0 :=
    coverEntropy_attractor_union_eq_zero q clock₀ sphere₀ vInf F R g
      hzeroInv hInfInv hR hg hREntropy hgEntropy
  apply coverEntropy_eq_zero_of_pointwise_attraction hF hK hKne hKInv hKEntropy
  intro x
  exact counterexample_attraction_of_coordinate_alternatives
    (fun n => F^[n] x) clock₀ sphere₀ sphereInf 0 (horbit x)

end Problem340

end

end OAI
