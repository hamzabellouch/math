import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Pullback
import OAI.Analysis.CoulombRadii.FieldAnalysis.JoinSpins

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
namespace Coulomb
lemma permute_join_block {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k))
    (x : Configuration m) (y : Configuration k) :
    permute (blockHom m k (p,q)) (joinConfiguration m k (x,y)) =
      joinConfiguration m k (permute p x, permute q y) := by
  ext ⟨i,b⟩
  refine Fin.addCases ?_ ?_ i
  · intro j
    change joinConfiguration m k (x,y) (blockHom m k (p,q) (Fin.castAdd k j),b) = _
    rw [blockHom_left, joinConfiguration_left, joinConfiguration_left]
    rfl
  · intro j
    change joinConfiguration m k (x,y) (blockHom m k (p,q) (Fin.natAdd m j),b) = _
    rw [blockHom_right, joinConfiguration_right, joinConfiguration_right]
    rfl

lemma spins_block_left {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k))
    (s : Spins (m+k)) :
    (s ∘ blockHom m k (p,q)) ∘ Fin.castAdd k = (s ∘ Fin.castAdd k) ∘ p := by
  funext i
  simp [Function.comp_def, blockHom_left]
lemma spins_block_right {m k : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin k))
    (s : Spins (m+k)) :
    (s ∘ blockHom m k (p,q)) ∘ Fin.natAdd m = (s ∘ Fin.natAdd m) ∘ q := by
  funext i
  simp [Function.comp_def, blockHom_right]

lemma tensor_block_covariance {m k : ℕ} (u : H1Vector m) (v : H1Vector k)
    (hu : Antisymmetric u) (hv : Antisymmetric v)
    (h : Equiv.Perm (Fin (m+k))) (hh : h ∈ blockGroup m k) (s : Spins (m+k)) :
    (u.tensor v).permutation h |>.value s =ᵐ[volume]
      fun x => ((h.sign : ℤ) : ℂ)*(u.tensor v).value s x := by
  rcases hh with ⟨⟨p,q⟩,rfl⟩
  have H1 : ∀ᵐ z : Configuration m × Configuration k ∂(volume.prod volume),
      u.value ((s ∘ Fin.castAdd k) ∘ p) (permute p z.1) =
        ((p.sign : ℤ) : ℂ)*u.value (s ∘ Fin.castAdd k) z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (hu p (s ∘ Fin.castAdd k))
  have H2 : ∀ᵐ z : Configuration m × Configuration k ∂(volume.prod volume),
      v.value ((s ∘ Fin.natAdd m) ∘ q) (permute q z.2) =
        ((q.sign : ℤ) : ℂ)*v.value (s ∘ Fin.natAdd m) z.2 :=
    Measure.quasiMeasurePreserving_snd.ae (hv q (s ∘ Fin.natAdd m))
  have H1' := (joinConfiguration_symm_measurePreserving m k).quasiMeasurePreserving.ae H1
  have H2' := (joinConfiguration_symm_measurePreserving m k).quasiMeasurePreserving.ae H2
  filter_upwards [H1',H2'] with x hx hy
  obtain ⟨⟨x,y⟩,rfl⟩ := (joinConfiguration m k).surjective x
  have hez : (joinConfiguration m k).symm.toHomeomorph.toMeasurableEquiv
      ((joinConfiguration m k) (x,y)) = (x,y) :=
    (joinConfiguration m k).symm_apply_apply (x,y)
  rw [hez] at hx hy
  change u.value ((s ∘ Fin.castAdd k) ∘ p) (permute p x) =
    ((p.sign : ℤ) : ℂ)*u.value (s ∘ Fin.castAdd k) x at hx
  change v.value ((s ∘ Fin.natAdd m) ∘ q) (permute q y) =
    ((q.sign : ℤ) : ℂ)*v.value (s ∘ Fin.natAdd m) y at hy
  rw [permutation_value]
  change tensorValue u v (s ∘ blockHom m k (p,q))
    (permute (blockHom m k (p,q)) (joinConfiguration m k (x,y))) =
    (((blockHom m k (p,q)).sign : ℤ) : ℂ)*tensorValue u v s (joinConfiguration m k (x,y))
  rw [permute_join_block, tensorValue_join, tensorValue_join, spins_block_left,
    spins_block_right, blockHom_sign, hx, hy]
  push_cast
  ring
lemma position_join_left {m k : ℕ} (x : Configuration m) (y : Configuration k) (i : Fin m) :
    position (joinConfiguration m k (x,y)) (Fin.castAdd k i) = position x i := by
  ext b
  exact joinConfiguration_left m k x y i b
lemma position_join_right {m k : ℕ} (x : Configuration m) (y : Configuration k) (i : Fin k) :
    position (joinConfiguration m k (x,y)) (Fin.natAdd m i) = position y i := by
  ext b
  exact joinConfiguration_right m k x y i b

lemma position_split_left {m k : ℕ} (x : Configuration (m+k)) (i : Fin m) :
    position ((joinConfiguration m k).symm x).1 i = position x (Fin.castAdd k i) := by
  obtain ⟨⟨y,z⟩,rfl⟩ := (joinConfiguration m k).surjective x
  rw [ContinuousLinearEquiv.symm_apply_apply, position_join_left]
lemma position_split_right {m k : ℕ} (x : Configuration (m+k)) (i : Fin k) :
    position ((joinConfiguration m k).symm x).2 i = position x (Fin.natAdd m i) := by
  obtain ⟨⟨y,z⟩,rfl⟩ := (joinConfiguration m k).surjective x
  rw [ContinuousLinearEquiv.symm_apply_apply, position_join_right]

def blockRegion (m k : ℕ) (A B : Set Space) : Set (Configuration (m+k)) :=
  {x | (∀ i : Fin m, position x (Fin.castAdd k i) ∈ A) ∧
    (∀ j : Fin k, position x (Fin.natAdd m j) ∈ B)}

lemma blockRegion_split {m k : ℕ} (A B : Set Space) (x : Configuration (m+k)) :
    x ∈ blockRegion m k A B ↔
      ((joinConfiguration m k).symm x).1 ∈ allPositions A ∧
      ((joinConfiguration m k).symm x).2 ∈ allPositions B := by
  simp only [blockRegion, allPositions, Set.mem_ofPred_eq, position_split_left,
    position_split_right]

lemma isClosed_blockRegion {m k : ℕ} {A B : Set Space} (hA : IsClosed A) (hB : IsClosed B) :
    IsClosed (blockRegion m k A B) := by
  have he : blockRegion m k A B =
      (⋂ i : Fin m, (fun x => position x (Fin.castAdd k i)) ⁻¹' A) ∩
      (⋂ j : Fin k, (fun x => position x (Fin.natAdd m j)) ⁻¹' B) := by
    ext x
    simp [blockRegion]
  rw [he]
  exact (isClosed_iInter (fun i => hA.preimage (continuous_position _))).inter
    (isClosed_iInter (fun j => hB.preimage (continuous_position _)))

lemma tensor_configSupported {m k : ℕ} (u : H1Vector m) (v : H1Vector k) (A B : Set Space)
    (hu : SpatiallySupported u A) (hv : SpatiallySupported v B) :
    ConfigSupported (u.tensor v) (blockRegion m k A B) := by
  intro s
  have H1 : ∀ᵐ z : Configuration m × Configuration k ∂(volume.prod volume),
      z.1 ∉ allPositions A → u.value (s ∘ Fin.castAdd k) z.1 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (hu (s ∘ Fin.castAdd k))
  have H2 : ∀ᵐ z : Configuration m × Configuration k ∂(volume.prod volume),
      z.2 ∉ allPositions B → v.value (s ∘ Fin.natAdd m) z.2 = 0 :=
    Measure.quasiMeasurePreserving_snd.ae (hv (s ∘ Fin.natAdd m))
  have H1' := (joinConfiguration_symm_measurePreserving m k).quasiMeasurePreserving.ae H1
  have H2' := (joinConfiguration_symm_measurePreserving m k).quasiMeasurePreserving.ae H2
  filter_upwards [H1',H2'] with x hx hy
  intro hn
  change u.value _ _ * v.value _ _ = 0
  change ((joinConfiguration m k).symm x).1 ∉ allPositions A →
    u.value (s ∘ Fin.castAdd k) ((joinConfiguration m k).symm x).1 = 0 at hx
  change ((joinConfiguration m k).symm x).2 ∉ allPositions B →
    v.value (s ∘ Fin.natAdd m) ((joinConfiguration m k).symm x).2 = 0 at hy
  by_cases ha : ((joinConfiguration m k).symm x).1 ∈ allPositions A
  · have hb : ((joinConfiguration m k).symm x).2 ∉ allPositions B :=
      fun h => hn ((blockRegion_split A B x).2 ⟨ha,h⟩)
    rw [hy hb, mul_zero]
  · rw [hx ha, zero_mul]

lemma blockRegion_orbit_disjoint {m k : ℕ} {A B : Set Space} (hAB : Disjoint A B)
    (p q : Equiv.Perm (Fin (m+k))) (hpq : p⁻¹*q ∉ blockGroup m k)
    (x : Configuration (m+k)) :
    ¬ (permute p x ∈ blockRegion m k A B ∧ permute q x ∈ blockRegion m k A B) := by
  rcases exists_crossing_of_not_mem (p⁻¹*q) hpq with ⟨i,j,hij⟩
  intro ⟨hp,hq⟩
  have he : q (Fin.castAdd k i) = p (Fin.natAdd m j) := by
    have H := congrArg p hij
    simpa using H
  have ha := hq.1 i
  have hb := hp.2 j
  rw [position_permute, he] at ha
  rw [position_permute] at hb
  exact Set.disjoint_left.1 hAB ha hb

lemma configSupported_value_orthogonal {n : ℕ} (u : H1Vector n) (R : Set (Configuration n))
    (hu : ConfigSupported u R) (p q : Equiv.Perm (Fin n))
    (hR : ∀ x, ¬(permute p x ∈ R ∧ permute q x ∈ R)) (s : Spins n) :
    ∀ᵐ x ∂volume, star ((u.permutation p).value s x)*(u.permutation q).value s x = 0 := by
  have hp := (permute_measurePreserving p).quasiMeasurePreserving.ae (hu (s ∘ p))
  have hq := (permute_measurePreserving q).quasiMeasurePreserving.ae (hu (s ∘ q))
  filter_upwards [hp,hq] with x hx hy
  rw [permutation_value, permutation_value]
  by_cases hpx : permute p x ∈ R
  · rw [hy (fun h => hR x ⟨hpx,h⟩), mul_zero]
  · rw [hx hpx, star_zero, zero_mul]

lemma configSupported_gradient_orthogonal {n : ℕ} (u : H1Vector n) (R : Set (Configuration n))
    (hu : ConfigSupported u R) (hclosed : IsClosed R) (p q : Equiv.Perm (Fin n))
    (hR : ∀ x, ¬(permute p x ∈ R ∧ permute q x ∈ R)) (s : Spins n) (a : Fin n × Fin 3) :
    ∀ᵐ x ∂volume, star ((u.permutation p).gradient s a x)*(u.permutation q).gradient s a x = 0 := by
  have hp := (permute_measurePreserving p).quasiMeasurePreserving.ae
    (hu.gradient hclosed (s ∘ p) (p.symm a.1,a.2))
  have hq := (permute_measurePreserving q).quasiMeasurePreserving.ae
    (hu.gradient hclosed (s ∘ q) (q.symm a.1,a.2))
  filter_upwards [hp,hq] with x hx hy
  rw [permutation_gradient, permutation_gradient]
  by_cases hpx : permute p x ∈ R
  · rw [hy (fun h => hR x ⟨hpx,h⟩), mul_zero]
  · rw [hx hpx, star_zero, zero_mul]
end Coulomb

open scoped BigOperators ComplexConjugate

end

end OAI
