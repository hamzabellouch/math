import OAI.Analysis.NuclearUltrapower.PullbackMatching

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section Predecessors
variable {Γ Δ B E : Type u} [Group Γ] [Group Δ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (f : Γ →* Δ)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) [Finite (Γ ⧸ θ.range)] (t : Δ)
  (S : Finset Γ) (u : Δ → ℕ → unitary B) (ω : Ultrafilter ℕ)

include hθ in
theorem sequence_predecessors (κ a : ℝ) (hgap : HasKazhdanGap.{u,u} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ) (ha0 : 0 < a)
    (ht : ∀ g, f (θ g) * t = t * f g)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (π : ℕ → FiniteUnitaryRep.{u,u} Γ) (hirr : ∀ n, (π n).Irreducible)
    (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u (f g) n) a (π n)) :
    ∀ᶠ n in (ω : Filter ℕ), ∃ τ : FiniteUnitaryRep.{u,u} Γ,
      τ.Irreducible ∧ Matches ρ S (fun g => u (f g) n) a τ ∧ (π n).Embeds (τ.pull θ) := by
  classical
  let : Fintype (Γ ⧸ θ.range) := Fintype.ofFinite _
  have hu1 (n : ℕ) : u (f 1) n = 1 := by rw [map_one,h1]
  have humul (g h : Γ) : Tendsto
      (fun n => ‖(u (f (g*h)) n : B) - (u (f g) n : B)*(u (f h) n : B)‖)
      (ω : Filter ℕ) (𝓝 0) := by simpa only [map_mul] using hmul (f g) (f h)
  obtain ⟨ξ,hξ,hξinv⟩ := matched_vectors ρ S (fun g => u (f g)) π ω κ a hgap hS ha hω hu1 humul hm
  let α := fun n => rangeTwist θ hθ (π n)
  let η : ∀ n, TensorHilbert E (α n) := fun n => shiftVector ρ θ hθ (π n) (u t n) (ξ n)
  have hη (n : ℕ) : ‖η n‖ = 1 := by rw [LinearIsometry.norm_map,hξ]
  have hηinv (h : θ.range) : Tendsto
      (fun n => ‖matchingTuple ρ (fun h : θ.range => u (f h) n) (α n) h (η n) - η n‖)
      (ω : Filter ℕ) (𝓝 0) := by
    obtain ⟨g,rfl⟩ := (MonoidHom.ofInjective hθ).surjective h
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => shiftVector_displacement ρ f θ hθ t ht (π n) (fun g => u g n) g (ξ n))
    simp_rw [hξ,mul_one]
    simpa only [add_zero] using ((hmul (f (θ g)) t).add (hmul t (f g)) |>.add (hξinv g))
  let y := fun n => inductionSeed θ.range (α n) ρ (fun g => u (f g) n) (η n)
  have hy (n : ℕ) : 1 ≤ ‖y n‖ := by
    have hb := inductionSeed_norm_ge θ.range (α n) ρ (fun g => u (f g) n) (hu1 n) (η n)
    rw [hη] at hb
    exact hb
  have he : Tendsto (fun n => tupleEnergy S
      (matchingTuple ρ (fun g => u (f g) n) (finiteInduced θ.range (α n))) (y n))
      (ω : Filter ℕ) (𝓝 0) := by
    apply energy_tendsto_zero (ω : Filter ℕ) S
      (fun g n => matchingTuple ρ (fun g => u (f g) n) (finiteInduced θ.range (α n)) g) y
    intro s _
    exact inductionSeed_almostInvariant θ.range α ρ (fun g => u (f g)) ω η hη humul hηinv s
  have hea : ∀ᶠ n in (ω : Filter ℕ), tupleEnergy S
      (matchingTuple ρ (fun g => u (f g) n) (finiteInduced θ.range (α n))) (y n) < a :=
    (tendsto_order.mp he).2 a ha0
  filter_upwards [hea] with n hn
  have hmI : Matches ρ S (fun g => u (f g) n) a (finiteInduced θ.range (α n)) := by
    apply (matches_iff_homogeneous ρ S (fun g => u (f g) n) a _).mpr
    refine ⟨y n, hn.trans_le ?_⟩
    have hn2 : 1 ≤ ‖y n‖^2 := by nlinarith [hy n]
    nlinarith
  obtain ⟨τ,hτ,htau,hmtau⟩ := Matches.exists_irreducible ρ S (fun g => u (f g) n) _ hmI
  exact ⟨τ,hτ,hmtau,frobenius_predecessor θ hθ (hirr n) htau⟩

end Predecessors
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
universe u v
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)
  (a : ℝ) (θ : Monoid.End Γ)

omit [Nontrivial E] in
/-- The finite predecessor graph forces periodicity of every matched irreducible,
including the initial vertex even if it lies on a nonempty tail. -/
theorem periodic_of_finite_matches
    (hf : (matchClasses ρ S u a).Finite)
    (hp : ∀ π : FiniteUnitaryRep.{u,v} Γ, π.Irreducible → Matches ρ S u a π →
      ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧ Matches ρ S u a τ ∧ π.Embeds (τ.pull θ))
    (π : FiniteUnitaryRep.{u,v} Γ) (hπ : π.Irreducible) (hm : Matches ρ S u a π) :
    ∃ p : ℕ, 0 < p ∧ π.Equivalent (π.pull (θ^p)) := by
  classical
  let D := matchClasses ρ S u a
  let : Finite D := hf.to_subtype
  have hex (q : D) : ∃ τ : FiniteUnitaryRep.{u,v} Γ,
      τ.Irreducible ∧ Matches ρ S u a τ ∧
      Quotient.mk (FiniteUnitaryRep.classSetoid Γ) τ = q.1 := q.2
  choose σ hirr hmatch hclass using hex
  have hprev (q : D) : ∃ r : D, (σ q).Embeds ((σ r).pull θ) := by
    obtain ⟨τ,ht,hmt,he⟩ := hp (σ q) (hirr q) (hmatch q)
    let r : D := ⟨Quotient.mk (FiniteUnitaryRep.classSetoid Γ) τ,τ,ht,hmt,rfl⟩
    have hτ : τ.Equivalent (σ r) := Quotient.exact (hclass r).symm
    exact ⟨r,he.trans (hτ.embeds.pull θ)⟩
  let q : D := ⟨Quotient.mk (FiniteUnitaryRep.classSetoid Γ) π,π,hπ,hm,rfl⟩
  have he : π.Equivalent (σ q) := Quotient.exact (hclass q).symm
  obtain ⟨p,hp,hh⟩ := FiniteUnitaryRep.finite_predecessor_cycle σ hirr θ hprev q
  exact ⟨p,hp,he.trans (hh.trans (he.pull (θ^p)).symm)⟩
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u
section Predecessors
variable {Γ Δ B E : Type u} [Group Γ] [Group Δ] [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (f : Γ →* Δ)
  (θ : Monoid.End Γ) (hθ : Function.Injective θ) [Finite (Γ ⧸ θ.range)] (t : Δ)
  (S : Finset Γ) (u : Δ → ℕ → unitary B) (ω : Ultrafilter ℕ)

include hθ in
/-- Uniformity is extracted by selecting a bad representation at every bad
coordinate. The selected dimensions are not bounded. -/
theorem uniform_predecessors (κ a : ℝ) (hgap : HasKazhdanGap.{u,u} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ) (ha0 : 0 < a)
    (ht : ∀ g, f (θ g) * t = t * f g)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (π₀ : FiniteUnitaryRep.{u,u} Γ) (hirr₀ : π₀.Irreducible) :
    ∀ᶠ n in (ω : Filter ℕ), ∀ π : FiniteUnitaryRep.{u,u} Γ,
      π.Irreducible → Matches ρ S (fun g => u (f g) n) a π →
      ∃ τ : FiniteUnitaryRep.{u,u} Γ, τ.Irreducible ∧
        Matches ρ S (fun g => u (f g) n) a τ ∧ π.Embeds (τ.pull θ) := by
  classical
  by_contra h
  have hb := (ω.eventually_not).mpr h
  simp only [not_forall] at hb
  let bad (n : ℕ) (π : FiniteUnitaryRep.{u,u} Γ) : Prop := π.Irreducible ∧
    Matches ρ S (fun g => u (f g) n) a π ∧
    ¬ ∃ τ : FiniteUnitaryRep.{u,u} Γ, τ.Irreducible ∧
      Matches ρ S (fun g => u (f g) n) a τ ∧ π.Embeds (τ.pull θ)
  have hb' : ∀ᶠ n in (ω : Filter ℕ), ∃ π, bad n π := hb.mono fun n hn => by
    obtain ⟨π, hi, hm, hn⟩ := hn
    exact ⟨π, hi, hm, hn⟩
  let π : ℕ → FiniteUnitaryRep.{u,u} Γ := fun n =>
    if hn : ∃ π, bad n π then hn.choose else π₀
  have hirr (n : ℕ) : (π n).Irreducible := by
    dsimp only [π]
    split_ifs with hn
    · exact hn.choose_spec.1
    · exact hirr₀
  have hs : ∀ᶠ n in (ω : Filter ℕ), bad n (π n) := hb'.mono fun n hn => by
    dsimp only [π]
    rw [dite_eq_left hn]
    exact hn.choose_spec
  have hm := hs.mono fun _ hn => hn.2.1
  have hp := sequence_predecessors ρ f θ hθ t S u ω κ a hgap hS ha ha0 ht hω h1 hmul π hirr hm
  obtain ⟨n,hn,hpn⟩ := (hs.and hp).exists
  exact hn.2.2 hpn

include hθ in
/-- The finite-match mechanism excludes an aperiodic irrep appearing in the
ultrapower spectral support. -/
theorem contradiction_of_initial_match (κ a : ℝ)
    (hB : IsNuclear.{u,u} B) (hSne : S.Nonempty)
    (hκ0 : 0 < κ) (hκ : κ ≤ 4 * (S.card : ℝ))
    (hgap : HasKazhdanGap.{u,u} S κ) (hS : Subgroup.closure (S : Set Γ) = ⊤)
    (ha : a < κ) (ha0 : 0 < a) (ha' : a < κ^2 / (4 * (S.card : ℝ)))
    (ht : ∀ g, f (θ g) * t = t * f g)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (π : FiniteUnitaryRep.{u,u} Γ) (hirr : π.Irreducible)
    (haper : ∀ p : ℕ, 0 < p → ¬ π.Equivalent (π.pull (θ^p)))
    (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u (f g) n) a π) : False := by
  have hp := uniform_predecessors ρ f θ hθ t S u ω κ a hgap hS ha ha0 ht hω h1 hmul π hirr
  obtain ⟨n,hn,hmn⟩ := (hp.and hm).exists
  have hfin := matchClasses_finite ρ S (fun g => u (f g) n) ω hB κ a hSne hκ0 hκ hgap ha' hω
  obtain ⟨p,hp,he⟩ := periodic_of_finite_matches ρ S (fun g => u (f g) n) a θ hfin hn π hirr hmn
  exact haper p hp he

end Predecessors
end NuclearUltrapower
end
end

end OAI
