import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTransition
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.SparsePulseCurves

namespace OAI

/-! Finite pulse concatenation for the actual planar transition flow.
This gives whole-rectangle routing independently of the autonomous suspension. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped NNReal

theorem IsPlanarTransition.eqOn_of_candidate {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    {K : ℝ≥0} (hV : ∀ t, LipschitzWith K (V t))
    (a : ℝ) {b c : ℝ} (x : Plane) (γ : ℝ → Plane)
    (hc : ContinuousOn γ (Icc b c)) (he : γ b = Ψ a b x)
    (hγ : ∀ t ∈ Ico b c, HasDerivAt γ (V (a + t) (γ t)) t) :
    EqOn (fun t => Ψ a t x) γ (Icc b c) := by
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun t _ => (hV (a + t)).lipschitzOnWith)
    ((continuous_iff_continuousAt.mpr (fun t => (hΨ.ode a t x).continuousAt)).continuousOn)
    (fun t _ => (hΨ.ode a t x).hasDerivWithinAt) (fun _ _ => mem_univ _)
    hc (fun t ht => (hγ t ht).hasDerivWithinAt) (fun _ _ => mem_univ _) he.symm

theorem planar_transition_chain {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    {K : ℝ≥0} (hV : ∀ t, LipschitzWith K (V t)) (a : ℝ)
    {N : ℕ} {cuts : ℕ → ℝ} {γ : ℕ → ℝ → Plane} {p : ℕ → Plane} {x : Plane}
    (hzero : cuts 0 = 0) (hx : x = p 0)
    (hcuts : ∀ i < N, cuts i ≤ cuts (i + 1))
    (hstart : ∀ i < N, γ i (cuts i) = p i)
    (hend : ∀ i < N, γ i (cuts (i + 1)) = p (i + 1))
    (hc : ∀ i < N, ContinuousOn (γ i) (Icc (cuts i) (cuts (i + 1))))
    (hd : ∀ i < N, ∀ s ∈ Ico (cuts i) (cuts (i + 1)),
      HasDerivAt (γ i) (V (a + s) (γ i s)) s) :
    (∀ i ≤ N, Ψ a (cuts i) x = p i) ∧
      (∀ i < N, EqOn (fun s => Ψ a s x) (γ i) (Icc (cuts i) (cuts (i + 1)))) := by
  have ha : ∀ i ≤ N, Ψ a (cuts i) x = p i := by
    intro i
    induction i with
    | zero =>
        intro _
        rw [hzero, hΨ.initial, hx]
    | succ i ih =>
        intro hi
        have hi' : i < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi
        have he := hΨ.eqOn_of_candidate hV a x (γ i) (hc i hi')
          ((hstart i hi').trans (ih (Nat.le_of_lt hi')).symm) (hd i hi')
        have hh := he ⟨hcuts i hi', le_rfl⟩
        simpa only [hend i hi', Nat.succ_eq_add_one] using hh
  refine ⟨ha, ?_⟩
  intro i hi
  exact hΨ.eqOn_of_candidate hV a x (γ i) (hc i hi)
    ((hstart i hi).trans (ha i (Nat.le_of_lt hi)).symm) (hd i hi)

namespace PlanarRouting

theorem sparse_planarTransition {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hΨ : IsPlanarTransition V Ψ)
    {K : ℝ≥0} (hV : ∀ t, LipschitzWith K (V t))
    {m n N : ℕ} (hN : 0 < N) (hn : n ≤ N)
    {J : Fin m → Fin n} (hJ : StrictMono J)
    (p : Fin (m + 1) → Plane) (γ : Fin m → ℝ → Plane) (cuts : ℕ → ℝ)
    (hzero : cuts 0 = 0) (hone : cuts N = 1)
    (hcuts : ∀ i < N, cuts i ≤ cuts (i + 1))
    (hstart : ∀ k, γ k (cuts (J k).val) = p k.castSucc)
    (hfinish : ∀ k, γ k (cuts ((J k).val + 1)) = p k.succ)
    (hc : ∀ k, ContinuousOn (γ k) (Icc (cuts (J k).val) (cuts ((J k).val + 1))))
    (hd : ∀ k s, s ∈ Ico (cuts (J k).val) (cuts ((J k).val + 1)) →
      HasDerivAt (γ k) (V s (γ k s)) s)
    (hz : ∀ i < N, (∀ k, (J k).val ≠ i) →
      ∀ s ∈ Ico (cuts i) (cuts (i + 1)), V s (sparseAnchor J p i) = 0)
    {S : Set Plane} (hp : ∀ k, p k ∈ S)
    (hmem : ∀ k s, s ∈ Icc (cuts (J k).val) (cuts ((J k).val + 1)) → γ k s ∈ S) :
    Ψ 0 1 (p 0) = p (Fin.last m) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, Ψ 0 s (p 0) ∈ S := by
  have h := planar_transition_chain hΨ hV 0 (N := N) (cuts := cuts)
    (γ := sparseCurve J p γ) (p := sparseAnchor J p) (x := p 0) hzero
    (by rw [sparseAnchor_zero]) hcuts
    (fun i _ => (sparseCurve_endpoints hJ p γ cuts hstart hfinish i).1)
    (fun i _ => (sparseCurve_endpoints hJ p γ cuts hstart hfinish i).2)
    (fun i _ => sparseCurve_continuousOn hJ p γ cuts hc i)
    (fun i hi s hs => by
      simpa only [zero_add] using sparseCurve_ode hJ p γ cuts V hd i s hs
        (fun hne => hz i hi hne s hs))
  constructor
  · have he := h.1 N le_rfl
    rw [hone, sparseAnchor_after_last J p hn] at he
    exact he
  · intro s hs
    cases N with
    | zero => omega
    | succ l =>
        obtain ⟨i, hi, his⟩ := finite_cuts_cover l cuts hcuts
          (by simpa only [hzero, hone] using hs)
        have he : Ψ 0 s (p 0) = sparseCurve J p γ i s := h.2 i hi his
        rw [he]
        exact sparseCurve_mem hJ p γ cuts hp hmem i s his

end PlanarRouting
end ForcedComputation

end

end OAI
