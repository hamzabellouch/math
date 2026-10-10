import OAI.Algebra.OddKaplansky.OrderedBlocks

namespace OAI

universe portUniverse1 portUniverse2

section
namespace OddKaplansky.OrderedSectorOrbit
noncomputable section
open scoped Classical BigOperators Matrix
open WreathFourier OrderedCosetCoordinates
variable {K : Type portUniverse1} {H : Type portUniverse2} [Field K] [Group H] [Fintype H] [LinearOrder H]
local instance orderedOrbitDecidableEq : DecidableEq H := Classical.decEq H
variable (M : ℕ) [NeZero M] {ζ : K} (hζ : IsPrimitiveRoot ζ M)
@[instance_reducible]
def action : MulAction H (Base (H := H) M) where
  smul g a := shift M g a
  one_smul a := by change shift M 1 a=a; rw [shift_one]; rfl
  mul_smul g h a := shift_mul M g h a
local instance : MulAction H (Base (H := H) M) := action M
abbrev Rep := OrbitSelection.Rep (H := H) (fun a : Base (H := H) M => SectorFourier.weight M a=1)
@[instance_reducible]
def characterOrder : LinearOrder (Base (H := H) M) := @FiniteChoice.functionOrder H (Fourier.C M) inferInstance inferInstance (SourceOrders.cyclic M)
def lmb (r : Rep (H := H) M) : Base (H := H) M := OrbitSelection.Ordered.representative (H := H) (characterOrder M) _ r
lemma lmb_spec (r : Rep (H := H) M) :
    (Quotient.mk'' (lmb M r) : MulAction.orbitRel.Quotient H (Base (H := H) M))=r.val ∧ SectorFourier.weight M (lmb M r)=1 :=
  OrbitSelection.Ordered.representative_spec (characterOrder M) _ r
lemma cover (a : Base (H := H) M) (ha : SectorFourier.weight M a=1) : ∃ r : Rep (H := H) M, ∃ h : H, shift M h (lmb M r)=a := by
  let r : Rep (H := H) M := ⟨Quotient.mk'' a,⟨a,rfl,ha⟩⟩
  refine ⟨r,?_⟩
  have hh : (Quotient.mk'' a : MulAction.orbitRel.Quotient H (Base (H := H) M))=Quotient.mk'' (lmb M r) := (lmb_spec M r).1.symm
  exact Quotient.exact hh
lemma lmb_weight (r : Rep (H := H) M) : SectorFourier.weight M (lmb M r)=1 := (lmb_spec M r).2
def T (r : Rep (H := H) M) : Subgroup H := MulAction.stabilizer H (lmb M r)
lemma mem_T (r : Rep (H := H) M) (g : H) : g ∈ T M r ↔ shift M g (lmb M r)=lmb M r := Iff.rfl
lemma separate {r s : Rep (H := H) M} (hrs : r≠s) (g : H) : lmb M r ≠ shift M g (lmb M s) := by
  intro he
  apply hrs
  apply Subtype.ext
  have hh : (Quotient.mk'' (lmb M r) : MulAction.orbitRel.Quotient H (Base (H := H) M)) = Quotient.mk'' (lmb M s) :=
    Quotient.sound ⟨g,he.symm⟩
  exact (lmb_spec M r).1.symm.trans (hh.trans (lmb_spec M s).1)
def orbitMap (z : (r : Rep (H := H) M) × (H ⧸ T M r)) :
    {a : Base (H := H) M // SectorFourier.weight M a=1} :=
  ⟨shift M (rep (T M z.1) z.2) (lmb M z.1), (SectorFourier.weight_shift M _ _).trans (lmb_weight M _)⟩
lemma orbitMap_injective : Function.Injective (orbitMap (H := H) M) := by
  rintro ⟨r,q⟩ ⟨s,t⟩ he
  have hv := congrArg Subtype.val he
  have hrs : r=s := by
    by_contra hn
    apply separate M hn ((rep (T M r) q)⁻¹ * rep (T M s) t)
    have hh := congrArg (shift M (rep (T M r) q)⁻¹) hv
    simpa only [orbitMap,← shift_mul,inv_mul_cancel,shift_one,MulEquiv.refl_apply] using hh
  subst s
  have hqt := (OrderedOrbitBlock.shift_eq_iff M (lmb M r) (T M r) (mem_T M r) _ _).mp hv
  rw [rep_mk,rep_mk] at hqt
  exact Sigma.mk.inj_iff.mpr ⟨rfl,heq_of_eq hqt⟩
lemma orbitMap_surjective : Function.Surjective (orbitMap (H := H) M) := by
  intro a
  obtain ⟨r,g,hg⟩ := cover M a.val a.property
  have hg' : shift M g (lmb M r)=a.val := hg
  refine ⟨⟨r,(g : H ⧸ T M r)⟩,?_⟩
  apply Subtype.ext
  change shift M (rep (T M r) (g : H ⧸ T M r)) (lmb M r)=a.val
  rw [← hg']
  exact (OrderedOrbitBlock.shift_eq_iff M (lmb M r) (T M r) (mem_T M r) _ _).mpr (rep_mk _ _)
def orbitEquiv : ((r : Rep (H := H) M) × (H ⧸ T M r)) ≃
    {a : Base (H := H) M // SectorFourier.weight M a=1} :=
  Equiv.ofBijective (orbitMap M) ⟨orbitMap_injective M,orbitMap_surjective M⟩
lemma identity_sum (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
    (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    ∑ r : Rep (H := H) M, OrderedOrbitBlock.identity M hζ (lmb M r) (T M r) = SectorFourier.f M hζ := by
  apply Eq.trans ?_ (SectorFourier.f_eq_packet (H := H) M hζ hc hm).symm
  have hh := Equiv.sum_comp (orbitEquiv (H := H) M) (fun a => projector M hζ a.val)
  change (∑ z : (r : Rep (H := H) M) × (H ⧸ T M r), projector M hζ (shift M (rep (T M z.1) z.2) (lmb M z.1))) = _ at hh
  simpa only [Fintype.sum_sigma,OrderedOrbitBlock.identity] using hh

variable (hc : (Fintype.card (Base (H := H) M) : K) ≠ 0)
abbrev Block (r : Rep (H := H) M) := Matrix (H ⧸ T M r) (H ⧸ T M r) (MonoidAlgebra K (T M r))
def pack : ((r : Rep (H := H) M) → Block (K := K) M r) →ₗ[K] MonoidAlgebra K (Wreath (H := H) M) where
  toFun F := ∑ r, OrderedOrbitBlock.lift M hζ (lmb M r) (T M r) (F r)
  map_add' F G := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c F := by simp only [Pi.smul_apply,map_smul,RingHom.id_apply,Finset.smul_sum]
lemma pack_apply (F : (r : Rep (H := H) M) → Block (K := K) M r) :
    pack M hζ F = ∑ r, OrderedOrbitBlock.lift M hζ (lmb M r) (T M r) (F r) := rfl
include hc in
lemma pack_mul (F G : (r : Rep (H := H) M) → Block (K := K) M r) :
    pack M hζ F * pack M hζ G = pack M hζ (fun r => F r*G r) := by
  rw [pack_apply,pack_apply,Finset.sum_mul,pack_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum,Finset.sum_eq_single r]
  · exact OrderedOrbitBlock.lift_mul M hζ hc (lmb M r) (T M r) (mem_T M r) (F r) (G r)
  · intro s _ hsr
    exact OrderedOrbitBlock.lift_cross M hζ hc (lmb M r) (T M r) (lmb M s) (T M s) (separate M hsr.symm) (F r) (G s)
  · simp
include hc in
lemma pack_one (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    pack (H := H) M hζ (fun _ => 1) = SectorFourier.f M hζ := by
  simp only [pack_apply,OrderedOrbitBlock.lift_one]
  exact identity_sum M hζ hc hm
include hc in
lemma pack_representation (e : MonoidAlgebra K H) (hm : (Fintype.card (Fourier.C M) : K) ≠ 0) :
    pack M hζ (fun r => OrderedCosetMatrix.representation (T M r) e) =
      SectorFourier.f M hζ * MonoidAlgebra.mapDomainAlgHom K K (top M) e := by
  simp only [pack_apply,OrderedOrbitBlock.lift_representation,← Finset.sum_mul,identity_sum M hζ hc hm]
end
end OddKaplansky.OrderedSectorOrbit

end

end OAI
