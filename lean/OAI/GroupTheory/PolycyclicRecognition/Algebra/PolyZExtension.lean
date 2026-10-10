import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolyZ

namespace OAI

/-! # Extending a torsion-free cyclic series by one cyclic quotient -/

noncomputable section
namespace PolycyclicRecognition

open ChromaticCyclic
variable {G J : Type} [Group G] [Group J]

theorem cyclicStep_factorMap_injective {H K : Subgroup G} (s : CyclicStep H K)
    (f : G →* J) (hf : Function.Injective f) :
    letI := s.normal
    letI := s.normal_map f
    Function.Injective (s.factorMap f) := by
  let := s.normal
  let := s.normal_map f
  apply (s.factorMap f).ker_eq_bot_iff.mp
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
  change (↑(⟨f x.val, Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩⟩ : K.map f) :
    K.map f ⧸ (H.map f).subgroupOf (K.map f)) = 1 at hx
  have hm := (QuotientGroup.eq_one_iff
    (⟨f x.val, Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩⟩ : K.map f)).mp hx
  obtain ⟨y, hy, he⟩ := hm
  have hxy : y = x.val := hf he
  change (↑x : K ⧸ H.subgroupOf K) = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  change (x : G) ∈ H
  rw [← hxy]
  exact hy

theorem TorsionFreeCyclicFactors.map {H K : Subgroup G} {n : ℕ}
    {c : CyclicSeries H K n} (hc : TorsionFreeCyclicFactors c)
    (f : G →* J) (hf : Function.Injective f) : TorsionFreeCyclicFactors (c.map f) := by
  dsimp only [TorsionFreeCyclicFactors, CyclicSeries.map]
  intro i hi
  let := (c.step i hi).normal
  let := (c.step i hi).normal_map f
  let e := MulEquiv.ofBijective ((c.step i hi).factorMap f)
    ⟨cyclicStep_factorMap_injective (c.step i hi) f hf,
      (c.step i hi).factorMap_surjective f⟩
  exact (hc i hi).of_injective e.symm.toMonoidHom e.symm.injective

def cyclicSeriesSnoc {H K L : Subgroup G} {n : ℕ}
    (c : CyclicSeries H K n) (s : CyclicStep K L) : CyclicSeries H L (n + 1) where
  group i := if i ≤ n then c.group i else L
  first := by simpa using c.first
  last := by simp
  step i hi := by
    by_cases h : i < n
    · simpa only [ite_eq_left (show i ≤ n by omega), ite_eq_left (show i + 1 ≤ n by omega)]
        using c.step i h
    · have he : i = n := by omega
      subst i
      simpa only [ite_eq_left le_rfl, ite_eq_right (show ¬n + 1 ≤ n by omega), c.last] using s

theorem cyclicStep_torsionFree_congr {H K H' K' : Subgroup G}
    (s : CyclicStep H K) (t : CyclicStep H' K') (hH : H = H') (hK : K = K') :
    (letI := s.normal; HasNoNontrivialTorsion (K ⧸ H.subgroupOf K)) ↔
      (letI := t.normal; HasNoNontrivialTorsion (K' ⧸ H'.subgroupOf K')) := by
  subst H'
  subst K'
  rfl

theorem TorsionFreeCyclicFactors.snoc {H K L : Subgroup G} {n : ℕ}
    {c : CyclicSeries H K n} (hc : TorsionFreeCyclicFactors c) (s : CyclicStep K L)
    (hs : letI := s.normal; HasNoNontrivialTorsion (L ⧸ K.subgroupOf L)) :
    TorsionFreeCyclicFactors (cyclicSeriesSnoc c s) := by
  intro i hi
  by_cases h : i < n
  · have h₀ : (cyclicSeriesSnoc c s).group i = c.group i :=
      ite_eq_left (by omega)
    have h₁ : (cyclicSeriesSnoc c s).group (i + 1) = c.group (i + 1) :=
      ite_eq_left (by omega)
    exact (cyclicStep_torsionFree_congr ((cyclicSeriesSnoc c s).step i hi)
      (c.step i h) h₀ h₁).mpr (hc i h)
  · have he : i = n := by omega
    subst i
    have h₀ : (cyclicSeriesSnoc c s).group n = K := by
      change (if n ≤ n then c.group n else L) = K
      rw [ite_eq_left le_rfl, c.last]
    have h₁ : (cyclicSeriesSnoc c s).group (n + 1) = L := ite_eq_right (by omega)
    exact (cyclicStep_torsionFree_congr ((cyclicSeriesSnoc c s).step n hi)
      s h₀ h₁).mpr hs

theorem isPolyZ_of_normal_cyclic_quotient (N : Subgroup G) [N.Normal]
    [IsCyclic (G ⧸ N)] (hN : IsPolyZ N)
    (hQ : HasNoNontrivialTorsion (G ⧸ N)) : IsPolyZ G := by
  obtain ⟨n, c, hc⟩ := hN
  let d := c.map N.subtype
  let d' : CyclicSeries (⊥ : Subgroup G) N n :=
    { d with
      first := by simpa only [Subgroup.map_bot] using d.first
      last := by simpa only [← MonoidHom.range_eq_map, N.range_subtype] using d.last }
  let s : CyclicStep N ⊤ := by
    have hbot : (⊥ : Subgroup (G ⧸ N)).comap (QuotientGroup.mk' N) = N := by
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    simpa only [hbot, Subgroup.comap_top] using
      (CyclicStep.bot (⊤ : Subgroup (G ⧸ N))).comap (QuotientGroup.mk' N)
  let := s.normal
  have hs : HasNoNontrivialTorsion ((⊤ : Subgroup G) ⧸ N.subgroupOf ⊤) := by
    let f : (⊤ : Subgroup G) ⧸ N.subgroupOf ⊤ →* G ⧸ N :=
      QuotientGroup.map _ _ (⊤ : Subgroup G).subtype (by intro x hx; exact hx)
    have hf : Function.Injective f := by
      apply f.ker_eq_bot_iff.mp
      apply le_antisymm ?_ bot_le
      intro x hx
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
      change QuotientGroup.mk' N (x : G) = 1 at hx
      exact (QuotientGroup.eq_one_iff x).mpr ((QuotientGroup.eq_one_iff (x : G)).mp hx)
    exact hQ.of_injective f hf
  have hd : TorsionFreeCyclicFactors d' := hc.map N.subtype N.subtype_injective
  exact ⟨n + 1, cyclicSeriesSnoc d' s, hd.snoc s hs⟩

end PolycyclicRecognition

end

end OAI
