import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingTwoAnnuli
import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereCollision
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingLogTime

namespace OAI

/-!
# Selecting a nontrivial shearing sequence from two annuli

This is the last compactness step in the two-scale argument of EKL,
Section 4.5. A scale tending to zero makes every annular return diverge.
The two-scale estimate selects a return with uniformly positive
displacement; the common upper scale controls its entire trajectory.
On a compact set with the stated horospherical separation property this
contradicts arithmetic freeness. The separation property is a separate
input here, not a claim that the low-entropy product theorem is proved.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma abs_tendsto_atTop_of_vanishing_scale
    (k t : ℕ → ℝ) (hk : Tendsto k atTop (𝓝 0))
    (hk0 : ∀ m, 0 ≤ k m) (ρ : ℝ) (hρ : 0 < ρ)
    (hlo : ∀ m, ρ ≤ k m * |t m|) :
    Tendsto (fun m => |t m|) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  by_cases hb : b ≤ 0
  · exact Eventually.of_forall fun m => hb.trans (abs_nonneg _)
  · have hbpos : 0 < b := lt_of_not_ge hb
    have he : ∀ᶠ m in atTop, k m < ρ / b :=
      (tendsto_order.1 hk).2 _ (div_pos hρ hbpos)
    filter_upwards [he] with m hm
    by_contra h
    have htb : |t m| ≤ b := (lt_of_not_ge h).le
    have hprod := mul_le_mul_of_nonneg_left htb (hk0 m)
    have hkb : k m * b < ρ := (lt_div_iff₀ hbpos).mp hm
    linarith [hlo m]

theorem no_two_annular_shearing_pairs_on_free_compact
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (hfree : ∀ z ∈ K, ∀ v ∈ pointLattice z, v ≠ 0 → ∀ k, v k ≠ 0)
    (hsep : ∀ z ∈ K, ∀ h : G n, RootHorosphereShape i j h → rightAction z h ∈ K →
      F z = F (rightAction z h) → rightAction z h = z)
    (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (hkpos : ∀ m, 0 < rootShearingKappa i j (g m))
    (hksmall : ∀ m, rootShearingKappa i j (g m) ≤ 1)
    (x : ℕ → Fin 2 → X n) (t : ℕ → Fin 2 → ℝ)
    (ρ C : ℝ) (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hlo : ∀ m q, ρ ≤ |rootShearingKappa i j (g m) * t m q|)
    (hfirst : ∀ m, |rootShearingKappa i j (g m) * t m 0| ≤ 1)
    (hsecond : ∀ m, 16 / ρ ≤ |rootShearingKappa i j (g m) * t m 1|)
    (hupp : ∀ m q, |rootShearingKappa i j (g m) * t m q| ≤ C)
    (hx : ∀ m q, x m q ∈ K)
    (hy : ∀ m q, rightAction (x m q)
      (Matrix.SpecialLinearGroup.transvection hij (t m q) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m q)) ∈ K)
    (heq : ∀ m q, F (x m q) = F (rightAction (x m q)
      (Matrix.SpecialLinearGroup.transvection hij (t m q) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m q)))) : False := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Fin.pos i
  let a : ℝ := ρ / (16 * (n : ℝ))
  have ha : 0 < a := div_pos hρ (by positivity)
  have hchoice (m : ℕ) : ∃ q : Fin 2, a ≤ rootShearSize hij (g m) (t m q) := by
    rcases rootShearSize_two_scales_lower hij (g m) (hkpos m)
      (t m 0) (t m 1) ρ hρ hρone (hlo m 0) (hfirst m) (hsecond m) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  choose q hq using hchoice
  have hk : Tendsto (fun m => rootShearingKappa i j (g m)) atTop (𝓝 0) := by
    change Tendsto (rootShearingKappa i j ∘ g) atTop (𝓝 0)
    simpa only [rootShearingKappa_one hij] using
      ((continuous_rootShearingKappa i j).tendsto 1).comp hg
  have hnorm (m : ℕ) :
      ρ ≤ rootShearingKappa i j (g m) * |t m (q m)| := by
    simpa only [abs_mul, abs_of_pos (hkpos m)] using hlo m (q m)
  have ht (m : ℕ) : t m (q m) ≠ 0 := by
    intro he
    have h := hnorm m
    rw [he, abs_zero, mul_zero] at h
    exact hρ.not_ge h
  apply no_signed_shearing_pairs_on_free_compact hij K hK F hF hfree hsep
    (fun m => x m (q m)) g hg (fun m => t m (q m)) ht
    (abs_tendsto_atTop_of_vanishing_scale _ _ hk (fun m => (hkpos m).le) ρ hρ hnorm)
    a ((n : ℝ) * n * (2 * C + C ^ 2)) ha hq
  · intro m u hu
    apply rootShearSize_bound_on_symmetric_interval hij (g m) (hksmall m)
      (t m (q m)) C _ u hu
    simpa only [abs_mul, abs_of_pos (hkpos m), mul_comm] using hupp m (q m)
  · exact fun m => hx m (q m)
  · exact fun m => hy m (q m)
  · exact fun m => heq m (q m)

end DukePrimeDegree

end

end OAI
