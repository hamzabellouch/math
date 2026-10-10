import Mathlib

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.EquivariantCoordinates
variable {Λ N T V : Type*} [Group Λ] [Group N] [Group T] [MulAction Λ V]

lemma hom_eq_of_smul_eq (a : Λ →* T)
    (hstab : ∀ (g : Λ) (v : V), g • v=v → a g=1) (g h : Λ) (v : V)
    (heq : g • v=h • v) : a g=a h := by
  have hs : (g⁻¹*h) • v=v := by rw [mul_smul,← heq,inv_smul_smul]
  have hh := hstab (g⁻¹*h) v hs
  rw [map_mul,map_inv,inv_mul_eq_one] at hh
  exact hh

lemma stabilizer_killed [IsMulTorsionFree T] (ρ : Λ →* N) (φ : N →* T)
    (hfinite : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite) :
    ∀ (g : Λ) (v : V), g • v=v → (φ.comp ρ) g=1 := by
  intro g v hg
  let H := (MulAction.stabilizer Λ v).map ρ
  have hmem : ρ g ∈ H := ⟨g,hg,rfl⟩
  let : Finite H := (hfinite v).to_subtype
  have hh := isOfFinOrder_of_finite (⟨ρ g,hmem⟩ : H)
  have hm := ((φ.comp H.subtype).isOfFinOrder hh).eq_one'
  exact hm

theorem exists_equivariant (a : Λ →* T)
    (hstab : ∀ (g : Λ) (v : V), g • v=v → a g=1) :
    ∃ π : V → T, ∀ g v, π (g • v)=a g*π v := by
  let q : V → MulAction.orbitRel.Quotient Λ V := Quotient.mk''
  let r : V → V := fun v => (q v).out
  have hex : ∀ v, ∃ g : Λ, g • r v=v := by
    intro v
    exact Quotient.exact (Quotient.out_eq' (q v)).symm
  choose b hb using hex
  let π : V → T := fun v => a (b v)
  refine ⟨π,?_⟩
  intro g v
  have hr : r (g • v)=r v := by
    apply congrArg Quotient.out
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  have hh : b (g • v) • r v=(g*b v) • r v := by
    rw [mul_smul,hb,← hr,hb]
  exact (hom_eq_of_smul_eq a hstab _ _ _ hh).trans (map_mul a g (b v))

lemma surjective_of_equivariant [Nonempty V] (a : Λ →* T)
    (ha : Function.Surjective a) (π : V → T)
    (hπ : ∀ g v, π (g • v)=a g*π v) : Function.Surjective π := by
  intro t
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨g,hg⟩ := ha (t*(π v)⁻¹)
  exact ⟨g • v,by rw [hπ,hg,inv_mul_cancel_right]⟩

lemma same_level_kernel_orbit (a : Λ →* T) (π : V → T)
    (hπ : ∀ g v, π (g • v)=a g*π v) (x y : V)
    (hxy : y ∈ MulAction.orbit Λ x) (heq : π y=π x) :
    y ∈ MulAction.orbit a.ker x := by
  obtain ⟨g,hg⟩ := hxy
  change g • x=y at hg
  have hga : a g=1 := by
    have hh := hπ g x
    rw [hg,heq] at hh
    have hmul : a g*π x=1*π x := by simpa only [one_mul] using hh.symm
    exact mul_right_cancel hmul
  exact ⟨⟨g,hga⟩,hg⟩

theorem finite_fibers (a : Λ →* T) (π : V → T)
    (hπ : ∀ g v, π (g • v)=a g*π v)
    (hker : ∀ v : V, (MulAction.orbit a.ker v).Finite)
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (t : T) : (π ⁻¹' {t}).Finite := by
  have hf : ∀ s : V, {v | π v=t ∧ v∈MulAction.orbit Λ s}.Finite := by
    intro s
    by_cases he : ∃ y, π y=t ∧ y∈MulAction.orbit Λ s
    · obtain ⟨y,hyt,hys⟩ := he
      apply (hker y).subset
      rintro v ⟨hvt,hvs⟩
      apply same_level_kernel_orbit a π hπ y v _ (hvt.trans hyt.symm)
      rw [MulAction.orbit_eq_iff.mpr hys]
      exact hvs
    · convert Set.finite_empty using 1
      ext v
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun h => he ⟨v,h⟩
  apply (hS.biUnion fun s _ => hf s).subset
  intro v hv
  obtain ⟨s,hs,hvs⟩ := hcover v
  exact Set.mem_iUnion₂.mpr ⟨s,hs,hv,hvs⟩

end CriticalPercolation.EquivariantCoordinates
end
end
end

end OAI
