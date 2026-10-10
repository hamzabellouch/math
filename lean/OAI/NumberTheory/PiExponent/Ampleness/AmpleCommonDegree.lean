import OAI.NumberTheory.PiExponent.Approximation.LinePowerLaws
import OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.common_degree (L : LineBundle X) {ι : Type} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (s : ∀ i, GlobalSections X (modulePow X L.sheaf (d i))) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : ι → GlobalSections X (modulePow X L.sheaf n),
      ∀ i, sectionOpen X (t i) = sectionOpen X (s i) := by
  classical
  let n := ∏ i, d i
  have hn : 0 < n := Finset.prod_pos (fun i _ => hd i)
  have hdiv (i : ι) : d i ∣ n := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have heq (i : ι) : d i * (n / d i) = n := Nat.mul_div_cancel' (hdiv i)
  let e (i : ι) : modulePow X (modulePow X L.sheaf (d i)) (n / d i) ≅
      modulePow X L.sheaf n :=
    linePowerMul L (d i) (n / d i) ≪≫ eqToIso (congrArg (modulePow X L.sheaf) (heq i))
  refine ⟨n, hn, fun i => powerSection (s i) (n / d i) ≫ (e i).hom, ?_⟩
  intro i
  change SectionOpens.isoOpen (powerSection (s i) (n / d i) ≫ (e i).hom) = _
  rw [SectionOpens.isoOpen_postcomp]
  exact (L.pow (d i)).sectionOpen_power (s i)
    (Nat.div_pos (Nat.le_of_dvd hn (hdiv i)) (hd i))

theorem LineBundle.ample_common_degree_cover [CompactSpace X] (L : LineBundle X)
    (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ l : ℕ,
      ∃ s : Fin l → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) := by
  classical
  have hex (x : X) := hL x ⊤ (by trivial)
  choose d hd s hs hst ha using hex
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hs x⟩)
  obtain ⟨n, hn, t, ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let e := (Fintype.equivFin I).symm
  refine ⟨n, hn, Fintype.card I, fun i => t (e i), ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    change x ∈ sectionOpen X (t (e (e.symm ⟨i, hi⟩)))
    rw [Equiv.apply_symm_apply, ht]
    exact hx
  · intro i
    rw [ht]
    exact ha (e i).val
  · intro i
    rw [ht]
    exact ⟨(e i).val, hs (e i).val⟩

end
end PiExponentSeshadri.Geometry

end OAI
