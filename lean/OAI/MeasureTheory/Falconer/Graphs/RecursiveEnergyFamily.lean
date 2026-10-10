import OAI.MeasureTheory.Falconer.Recursion.ActualDistanceRecursionBound
import OAI.MeasureTheory.Falconer.Estimates.SourceStateTerminal

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

structure RecursiveEnvironment where
  Q : DyadicSquare
  ρ : Measure Plane
  mass : ℝ → ℝ
  N : ℕ
  q : ℕ
  J : ℕ
  lam : ℝ
  sig : ℝ

namespace RecursiveEnvironment

noncomputable def profile (e : RecursiveEnvironment) (n : ℕ) : ℝ := e.mass n-(n:ℝ)/e.N

def distanceData (e : RecursiveEnvironment) (a t i : ℕ) (X Y : CellPath) : PositiveDistanceData :=
  ⟨e.Q,e.ρ,e.mass,e.N,e.q,a,t,e.lam,e.sig,e.J,i,X,Y⟩

def angularData (e : RecursiveEnvironment) (a₀ t₀ a v i : ℕ) (X Y : CellPath) : AngularStateData :=
  ⟨e.Q,e.ρ,e.mass,e.N,e.q,a₀,t₀,a,v,e.J,i,e.lam,e.sig,X,Y⟩

def energies (e : RecursiveEnvironment) (K : ℕ) (Ψ : ℝ → ℝ) : BranchState → ℝ → Prop
  | .D a t i, x => ∃ X Y : CellPath,
      (e.distanceData a t i X Y).RecursiveCells ∧
      x = (e.distanceData a t i X Y).coincidence.toReal
  | .H a₀ t₀ a v i, x => ∃ X Y : CellPath, X.length = a ∧ Y.length = a ∧
      ∃ k : Fin 2 → PolicyDescriptor → ℕ,
        (∀ l, ∑ b ∈ (e.angularData a₀ t₀ a v i X Y).retainedList a, k l b ≤ K) ∧
      ∃ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) ∧
        (∀ l y, ‖h l y‖ ≤ 1) ∧ x = ((e.angularData a₀ t₀ a v i X Y).energy k h Ψ).toReal

theorem energies_nonneg (e : RecursiveEnvironment) (K : ℕ) (Ψ : ℝ → ℝ)
    {s : BranchState} {x : ℝ} (hx : e.energies K Ψ s x) : 0 ≤ x := by
  cases s with
  | D a t i => obtain ⟨X,Y,_,rfl⟩ := hx; exact ENNReal.toReal_nonneg
  | H a₀ t₀ a v i => obtain ⟨X,Y,_,_,k,_,h,_,_,rfl⟩ := hx; exact ENNReal.toReal_nonneg

end RecursiveEnvironment

theorem uniform_recursive_energy_rules {lam sig kap eps tau T : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (htau : 0 < tau) (hT : 0 < T) (K₀ : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ K : ℕ, K₀ ≤ K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ e : RecursiveEnvironment,
      e.lam = lam → e.sig = sig → e.q = sourcePolicyBlock e.N kap →
      e.J = sourceSmoothingLevels sig kap → N₀ ≤ e.N → e.Q.side = 1 → e.ρ e.Q.carrierᶜ = 0 →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData e.Q e.ρ e.N B δ e.lam e.mass →
      (∀ s : BranchState, s.Valid e.N e.sig → s.finish ≤ s.start+100*e.q → ∀ x, e.energies K Ψ s x →
        x ≤ ((2:ℝ)^e.N)^(200*(e.q:ℝ)/e.N+12*lam+tau)) ∧
      (∀ s : BranchState, s.Valid e.N e.sig → s.index+1 ≤ e.J → s.start+100*e.q < s.finish →
        ∀ M : ℝ, 0 ≤ M → ((2:ℝ)^e.N)^(12*lam+eps) ≤ M →
        (∀ u l, BranchStep e.profile e.N e.q e.sig s l u → ∀ x, e.energies K Ψ u x →
          ((2:ℝ)^e.N)^(branchExponent e.profile lam sig eps s l u)*x ≤ M) →
        ∀ x, e.energies K Ψ s x → x ≤ ((e.N:ℝ)+3)*M+((2:ℝ)^e.N)^(-T)) := by
  obtain ⟨Kinv,N₁,h₁⟩ := uniform_actual_distance_recursion_bound hlam hsig hkap hgap heps
    (add_pos hT heps) hΨ hpos hs hone
  let K := max K₀ Kinv
  obtain ⟨N₂,h₂⟩ := uniform_actual_angular_recursion_bound hlam hsig hkap hgap heps T K hΨ hpos hs
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hWupper : ∀ x, Ψ x ≤ W := fun x => (le_abs_self _).trans (hWb x)
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  obtain ⟨N₃,hN₃,h₃⟩ := uniform_angular_state_terminal K htau hW Ψ hWupper hsupport
  refine ⟨K,le_max_left _ _,max N₁ (max N₂ N₃),by omega,?_⟩
  intro e hdlam hdsig hdq hdJ hN hQ hcarry B δ hprof
  have hNp : 0 < e.N := by omega
  have hQp : 0 < e.Q.side := by rw [hQ]; norm_num
  have heqp : 0 < e.q := by rw [hdq]; exact sourcePolicyBlock_pos hNp hkap
  constructor
  · intro s hv ht x hx
    cases s with
    | D a t i =>
      obtain ⟨X,Y,hcells,rfl⟩ := hx
      let d := e.distanceData a t i X Y
      have hb := d.terminal_power hprof hNp (hv.1.trans hv.2) hcells.1 hcells.2.1 ht htau.le
      simpa only [d,RecursiveEnvironment.distanceData,hdlam] using hb.2
    | H a₀ t₀ a v i =>
      obtain ⟨X,Y,hX,hY,k,hk,h,hh,hhb,rfl⟩ := hx
      have hb := h₃ (e.angularData a₀ t₀ a v i X Y) (show N₃ ≤ e.N by omega)
        hQp (hv.2.1.trans (hv.2.2.1.trans hv.2.2.2.1)) hX hY ht B δ hprof k hk h hh hhb
      simpa only [RecursiveEnvironment.angularData,hdlam] using hb.2
  · intro s hv hi hw M hM hfloor hchildren x hx
    cases s with
    | D a t i =>
      obtain ⟨X,Y,hcells,rfl⟩ := hx
      let d := e.distanceData a t i X Y
      have hb := h₁ K (le_max_right _ _) d hdlam hdsig hdq hdJ (show N₁ ≤ e.N by omega)
        hQ hcarry hcells hv hw hi B δ hprof M hM hfloor
      have hDc : ∀ t' i' l, BranchStep d.branchProfile d.N d.q d.sig d.branchState l (.D d.a t' i') →
          ((2:ℝ)^d.N)^(branchExponent d.branchProfile lam sig eps d.branchState l (.D d.a t' i')) *
            ({d with t := t',i := i'} : PositiveDistanceData).coincidence.toReal ≤ M := by
        intro t' i' l hstep
        exact hchildren _ l hstep _ ⟨X,Y,hcells.update t' i',rfl⟩
      have hHc : ∀ p v, ∀ row ∈ sourceProductVertices d.Q d.Q d.ρ d.ρ d.X d.Y (p-d.a),
          BranchStep d.branchProfile d.N d.q d.sig d.branchState .high (.H d.a d.t p v d.i) →
          ∀ k : Fin 2 → PolicyDescriptor → ℕ, (∀ l, ∑ b ∈ d.prefixRemainingList p, k l b ≤ K) →
          ∀ h : Fin 2 → Plane → ℂ, (∀ l, Measurable (h l)) → (∀ l y, ‖h l y‖ ≤ 1) →
          ((2:ℝ)^d.N)^(branchExponent d.branchProfile lam sig eps d.branchState .high (.H d.a d.t p v d.i)) *
            ((d.angularSuccessor p v row).energy k h Ψ).toReal ≤ M := by
        intro p v row hr hstep k hk h hh hhb
        have hap := (hstep.nested heqp hv).1
        have hl := d.angularSuccessor_lengths hap hcells.1 hcells.2.1 v hr
        exact hchildren _ .high hstep _ ⟨row.1,row.2,hl.1,hl.2,k,hk,h,hh,hhb,rfl⟩
      have hb := (hb hDc hHc).2
      have he : eps-(T+eps) = -T := by ring
      rw [he] at hb
      change _ ≤ ((e.N:ℝ)+3)*M+_
      exact hb.trans (by dsimp only [d,RecursiveEnvironment.distanceData]; nlinarith [Nat.cast_nonneg (α := ℝ) e.N])
    | H a₀ t₀ a v i =>
      obtain ⟨X,Y,hX,hY,k,hk,h,hh,hhb,rfl⟩ := hx
      let d := e.angularData a₀ t₀ a v i X Y
      have hb := h₂ d hdlam hdsig hdq hdJ (show N₂ ≤ e.N by omega) hQ hcarry hv hw hi
        hX hY B δ hprof k hk h hh hhb M hM
      have hHc : ∀ p l, BranchStep d.profile d.N d.q d.sig d.branchState l (.H d.a₀ d.t₀ p d.v d.i) →
          ∀ row ∈ d.children p,
          ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState l (.H d.a₀ d.t₀ p d.v d.i)) *
            ((d.successor p row).energy k h Ψ).toReal ≤ M := by
        intro p l hstep row hr
        have hap := (hstep.nested heqp hv).1
        have hl := d.children_lengths hap hX hY hr
        exact hchildren _ l hstep _ ⟨row.1,row.2,hl.1,hl.2,k,d.successor_budget hap row k hk,h,hh,hhb,rfl⟩
      have hDc : ∀ b, BranchStep d.profile d.N d.q d.sig d.branchState .far (.D b d.v (d.i+1)) →
          ∀ row ∈ d.children b, ∀ col ∈ d.children b, angularSeparated d.Q d.Q b row col →
          ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
            ((d.distanceSuccessor b).atCells row.1 col.1).coincidence.toReal ≤ M ∧
          ((2:ℝ)^d.N)^(branchExponent d.profile lam sig eps d.branchState .far (.D b d.v (d.i+1))) *
            ((d.distanceSuccessor b).atCells row.2 col.2).coincidence.toReal ≤ M := by
        intro b hstep row hr col hc hs
        have hab := (hstep.nested heqp hv).1
        have hcells := d.far_recursive_cells hab hX hY hr hc hs
        exact ⟨hchildren _ .far hstep _ ⟨row.1,col.1,hcells.1,rfl⟩,
          hchildren _ .far hstep _ ⟨row.2,col.2,hcells.2,rfl⟩⟩
      have hb := (hb hHc hDc).2
      exact hb.trans (by dsimp only [d,RecursiveEnvironment.angularData]; nlinarith)

end PlanarFalconer

end OAI
