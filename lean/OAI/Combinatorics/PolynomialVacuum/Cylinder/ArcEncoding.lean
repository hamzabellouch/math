import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcClassification
import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcPool
import OAI.Combinatorics.PolynomialVacuum.Cylinder.ArcNorm

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M H : ℕ} [NeZero M]
namespace BoundaryArc
noncomputable def shape (A : BoundaryArc (bandSites M H)) : ArcShape M :=
  if h : ∃B : PolynomialVacuumBridge.Corridor.ArchWord.CylinderArch M,B.val.word=A.word then .inl h.choose
  else .inr (A.word_shape.resolve_left h).choose

theorem shape_word (A : BoundaryArc (bandSites M H)) : A.shape.word=A.word := by
  unfold shape
  split_ifs with h
  · exact h.choose_spec
  · exact (A.word_shape.resolve_left h).choose_spec.1

theorem shape_mass (A : BoundaryArc (bandSites M H)) : A.shape.mass=‖A.weight‖ := by
  rw [ArcShape.mass,A.shape_word,A.norm_weight]

theorem eq_of_port_shape (A B : BoundaryArc (bandSites M H)) (hp : A.port=B.port) (hs : A.shape=B.shape) : A=B := by
  apply A.ext_data B
  · rw [A.start_port,B.start_port,hp]
  · have he:=congrArg ArcShape.word hs
    simpa only [shape_word] using he
end BoundaryArc
namespace ArcSystem
variable (S : ArcSystem (bandSites M H))

theorem port_injective : Set.InjOn (BoundaryArc.port (M:=M) (H:=H)) (S.val : Set (BoundaryArc (bandSites M H))) := by
  intro A hA B hB hp
  by_contra hn
  have hs : A.start=B.start := by rw [A.start_port,B.start_port,hp]
  exact Finset.disjoint_left.mp (S.property hA hB hn) A.start_mem (by rw [hs]; exact B.start_mem)

noncomputable def code (p : Bool × ZMod M) : ArcChoice M :=
  if h : ∃A∈S.val,A.port=p then .inr h.choose.shape else .inl ()

theorem code_member (A : BoundaryArc (bandSites M H)) (hA : A∈S.val) : S.code A.port=.inr A.shape := by
  have he : ∃B∈S.val,B.port=A.port := ⟨A,hA,rfl⟩
  rw [code,dite_eq_left he]
  have hh : he.choose=A := S.port_injective he.choose_spec.1 hA he.choose_spec.2
  rw [hh]

theorem code_empty (p : Bool × ZMod M) (he : ¬∃A∈S.val,A.port=p) : S.code p=.inl () := by
  simp [code,he]

theorem code_injective : Function.Injective (code (M:=M) (H:=H)) := by
  intro S T h
  apply Subtype.ext
  apply Finset.ext
  intro A
  have one (S T : ArcSystem (bandSites M H)) (h : S.code=T.code) (hA : A∈S.val) : A∈T.val := by
    have hc:=S.code_member A hA
    rw [h] at hc
    unfold code at hc
    split_ifs at hc with he
    · have hs : he.choose.shape=A.shape := Sum.inr.inj hc
      have hh:=he.choose.eq_of_port_shape A he.choose_spec.2 hs
      exact hh ▸ he.choose_spec.1
  exact ⟨one S T h,one T S h.symm⟩

theorem norm_weight_code : ‖S.weight‖=arcChoiceMajorant S.code := by
  have hi := S.port_injective
  have hm (A : BoundaryArc (bandSites M H)) (hA : A∈S.val) :
      ArcChoice.mass (S.code A.port)=‖A.weight‖ := by rw [S.code_member A hA]; exact A.shape_mass
  have he : (∏p∈S.val.image BoundaryArc.port,ArcChoice.mass (S.code p))=∏A∈S.val,‖A.weight‖ := by
    rw [Finset.prod_image hi]
    exact Finset.prod_congr rfl hm
  rw [ArcSystem.weight,norm_prod,← he]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro p _ hp
  have hn : ¬∃A∈S.val,A.port=p := by simpa only [Finset.mem_image] using hp
  rw [S.code_empty p hn]
  rfl
end ArcSystem
end PolynomialVacuumCylinder

end OAI
