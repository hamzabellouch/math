import Mathlib
import OAI.GroupTheory.PeriodicGroups.Frames.ExteriorComplex
import OAI.GroupTheory.PeriodicGroups.Presentation.MatrixStabilizers

namespace OAI

section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma card_quad_le (i j k l : ι) : ({i,j,k,l}:Finset ι).card ≤ 5 := by
  have h1 := Finset.card_insert_le i ({j,k,l}:Finset ι)
  have h2 := Finset.card_insert_le j ({k,l}:Finset ι)
  have h3 := Finset.card_insert_le k ({l}:Finset ι)
  simp only [Finset.card_singleton] at h3
  omega

lemma swap_inv (i j : ι) (h : i≠j) : (swap (R := R) i j h)⁻¹ = swap i j h :=
  (eq_inv_of_mul_eq_one_left (swap_square i j h)).symm

lemma swap_conjugate_root (a b : ι) (hab : a≠b) (i j : ι) (hij : i≠j) (r : R) :
    swap a b hab * root i j hij r * (swap a b hab)⁻¹ =
    root (Equiv.swap a b i) (Equiv.swap a b j) ((Equiv.swap a b).injective.ne hij) r := by
  let S : Finset ι := {a,b,i,j}
  have hs := swap_mem_local (R := R) S a b hab (by simp [S]) (by simp [S])
  have hr := root_mem_local S i j hij r (by simp [S]) (by simp [S])
  have hi : Equiv.swap a b i ∈ S := by simp only [Equiv.swap_apply_def]; split_ifs <;> simp [S]
  have hj : Equiv.swap a b j ∈ S := by simp only [Equiv.swap_apply_def]; split_ifs <;> simp [S]
  apply local_faithful S (card_quad_le _ _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem hs hr) ((localGroup S).inv_mem hs))
    (root_mem_local S _ _ _ _ hi hj)
  simpa only [map_mul,map_inv,evaluate_swap,evaluate_root] using permutation_conjugate_elementary (Equiv.swap a b) i j hij r

lemma swap_conjugate_diag (a b : ι) (hab : a≠b) (i : ι) (u : Rˣ) :
    swap a b hab * diag i u * (swap a b hab)⁻¹ = diag (Equiv.swap a b i) u := by
  let S : Finset ι := {a,b,i}
  have hs := swap_mem_local (R := R) S a b hab (by simp [S]) (by simp [S])
  have hd := diag_mem_local S i u (by simp [S])
  have hi : Equiv.swap a b i ∈ S := by simp only [Equiv.swap_apply_def]; split_ifs <;> simp [S]
  apply local_faithful S (card_triple_le _ _ _)
    ((localGroup S).mul_mem ((localGroup S).mul_mem hs hd) ((localGroup S).inv_mem hs))
    (diag_mem_local S _ _ hi)
  simpa only [map_mul,map_inv,evaluate_swap,evaluate_diag] using permutation_conjugate_diagonal (Equiv.swap a b) i u

lemma swap_mem_parabolic (t i j : ι) (hij : i≠j) (hi : i≠t) (hj : j≠t) :
    swap (R := R) i j hij∈parabolic t := by
  unfold swap
  exact (parabolic t).mul_mem ((parabolic t).mul_mem
    ((parabolic t).mul_mem (root_mem_parabolic t i j hij 1 hj) (root_mem_parabolic t j i hij.symm (-1) hi))
    (root_mem_parabolic t i j hij 1 hj)) (diag_mem_parabolic t i (-1) hi)

lemma parabolic_swap_generates (t a : ι) (hta : t≠a) :
    Subgroup.closure ((parabolic (R := R) t : Set (Group (ι := ι) (R := R))) ∪ {swap t a hta}) = ⊤ := by
  let P : Subgroup (Group (ι := ι) (R := R)) := Subgroup.closure ((parabolic (R := R) t : Set (Group (ι := ι) (R := R))) ∪ {swap t a hta})
  have hp : parabolic t ≤ P := fun _ hg => Subgroup.subset_closure (Or.inl hg)
  have hs : swap t a hta ∈ P := Subgroup.subset_closure (Or.inr rfl)
  apply top_unique
  rw [←supported_gen_all]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨g,rfl⟩
  cases g with
  | root i j h r =>
    change root i j h r ∈ P
    by_cases hj : j≠t
    · exact hp (root_mem_parabolic t i j h r hj)
    · have hjt := not_ne_iff.mp hj
      let p := Equiv.swap t a
      have hpa : p j≠t := by simp [p,hjt,hta.symm]
      have hm := P.mul_mem (P.mul_mem hs (hp (root_mem_parabolic t (p i) (p j) (p.injective.ne h) r hpa))) (P.inv_mem hs)
      rw [swap_conjugate_root] at hm
      simpa only [p,Equiv.swap_apply_self] using hm
  | diag i u =>
    change diag i u ∈ P
    by_cases hi : i≠t
    · exact hp (diag_mem_parabolic t i u hi)
    · have hit := not_ne_iff.mp hi
      let p := Equiv.swap t a
      have hpa : p i≠t := by simp [p,hit,hta.symm]
      have hm := P.mul_mem (P.mul_mem hs (hp (diag_mem_parabolic t (p i) u hpa))) (P.inv_mem hs)
      rw [swap_conjugate_diag] at hm
      simpa only [p,Equiv.swap_apply_self] using hm

def fixingGroup (S : Finset ι) : Subgroup (Group (ι := ι) (R := R)) :=
  Subgroup.closure ({g | ∃i j h a, j∉S ∧ g=root i j h a} ∪ {g | ∃i u, i∉S ∧ g=diag i u})

lemma fixingGroup_le_parabolic (S : Finset ι) (t : ι) (ht : t∈S) : fixingGroup (R := R) S ≤ parabolic t := by
  apply (Subgroup.closure_le _).mpr
  rintro x (⟨i,j,h,a,hj,rfl⟩ | ⟨i,u,hi,rfl⟩)
  · exact root_mem_parabolic t i j h a (fun he => hj (he ▸ ht))
  · exact diag_mem_parabolic t i u (fun he => hi (he ▸ ht))

lemma evaluate_fixingGroup [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) (S : Finset ι) : (fixingGroup (R := R) S).map evaluate = fixer S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨i,j,h,a,hj,rfl⟩ | ⟨i,u,hi,rfl⟩)
    · change evaluate (root i j h a) ∈ fixer S
      rw [evaluate_root]; exact elementary_mem_fixer _ _ _ _ _ hj
    · change evaluate (diag i u) ∈ fixer S
      rw [evaluate_diag]; exact singleDiagonal_mem_fixer _ _ _ hi
  · apply fixer_generated ε hI
    · intro i j h a hj
      exact ⟨root i j h a,Subgroup.subset_closure (Or.inl ⟨i,j,h,a,hj,rfl⟩),evaluate_root _ _ _ _⟩
    · intro i u hi
      exact ⟨diag i u,Subgroup.subset_closure (Or.inr ⟨i,u,hi,rfl⟩),evaluate_diag _ _⟩

lemma swap_conjugate_fixingGroup_le (t a : ι) (hta : t≠a) :
    fixingGroup (R := R) {t,a} ≤ (parabolic t).comap (MulAut.conj (swap t a hta)).toMonoidHom := by
  apply (Subgroup.closure_le _).mpr
  rintro x (⟨i,j,h,r,hj,rfl⟩ | ⟨i,u,hi,rfl⟩)
  · change swap t a hta * root i j h r * (swap t a hta)⁻¹ ∈ parabolic t
    rw [swap_conjugate_root]
    exact root_mem_parabolic _ _ _ _ _ (by
      have hjt : j≠t := fun he => hj (by simp [he])
      have hja : j≠a := fun he => hj (by simp [he])
      simpa only [Equiv.swap_apply_of_ne_of_ne hjt hja] using hjt)
  · change swap t a hta * diag i u * (swap t a hta)⁻¹ ∈ parabolic t
    rw [swap_conjugate_diag]
    exact diag_mem_parabolic _ _ _ (by
      have hit : i≠t := fun he => hi (by simp [he])
      have hia : i≠a := fun he => hi (by simp [he])
      simpa only [Equiv.swap_apply_of_ne_of_ne hit hia] using hit)

lemma swap_normalizes_double_fixer [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)
    (hI : MatrixNilKernel ε.toRingHom) (t a : ι) (hta : t≠a)
    (ih : Function.Injective (evaluate (ι := {i // i∈Finset.univ.erase t}) (R := R)))
    {g : Group (ι := ι) (R := R)} (hg : g∈parabolic t) (he : evaluate g∈fixer {t,a}) :
    (swap t a hta)⁻¹*g*swap t a hta∈parabolic t := by
  rw [←evaluate_fixingGroup ε hI] at he
  obtain ⟨q,hq,hqg⟩ := he
  have hqg' : q=g := parabolic_faithful t ih (fixingGroup_le_parabolic {t,a} t (by simp) hq) hg hqg
  subst g
  have hh := swap_conjugate_fixingGroup_le t a hta hq
  change swap t a hta * q * (swap t a hta)⁻¹ ∈ parabolic t at hh
  simpa only [swap_inv] using hh

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.FrameTransport
noncomputable section
open Classical
variable {V F W : Type*} [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)

def Edge (u v : V) : Prop := u ≠ v ∧ LinearIndepOn F ρ {u,v}

lemma Edge.symm {u v : V} (h : Edge (F := F) ρ u v) : Edge (F := F) ρ v u :=
  ⟨h.1.symm, by simpa [Set.pair_comm] using h.2⟩

lemma edge_outside {u v : V} (hu : ρ u ≠ 0)
    (hv : ρ v ∉ Submodule.span F (ρ '' {u})) : Edge (F := F) ρ u v := by
  refine ⟨?_, ?_⟩
  · intro he
    subst v
    exact hv (Submodule.subset_span ⟨u, by simp, rfl⟩)
  · have hi : LinearIndepOn F ρ ({u} : Set V) := (linearIndepOn_singleton_iff F).mpr hu
    simpa [Set.pair_comm] using hi.insert hv

lemma edge_to_cone {s : Set V} {v w : V} (hv : v ∈ s) (hn : ρ v ≠ 0)
    (hw : ρ w ∉ Submodule.span F (ρ '' s)) : Edge (F := F) ρ v w :=
  edge_outside ρ hn (fun he => hw (Submodule.span_mono (Set.image_mono (by simpa using hv)) he))

lemma triangle_to_cone {s : Set V} {u v w : V} (hu : u ∈ s) (hv : v ∈ s)
    (huv : Edge (F := F) ρ u v) (hw : ρ w ∉ Submodule.span F (ρ '' s)) :
    LinearIndepOn F ρ {u,v,w} := by
  have hx : ρ w ∉ Submodule.span F (ρ '' ({u,v} : Set V)) := by
    have hsub : ({u,v} : Set V) ⊆ s := by
      intro x hx
      rcases hx with rfl | hx
      · exact hu
      · exact Set.mem_singleton_iff.mp hx ▸ hv
    exact fun he => hw (Submodule.span_mono (Set.image_mono hsub) he)
  have hi := huv.2.insert hx
  have he : ({u,v,w} : Set V) = insert w {u,v} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [he]
  exact hi

structure FlatSystem (A : V → Type*) where
  step : ∀ (u v : V), Edge (F := F) ρ u v → A u ≃ A v
  reverse : ∀ (u v : V) (h : Edge (F := F) ρ u v),
    (step u v h).trans (step v u (h.symm ρ)) = Equiv.refl (A u)
  triangle : ∀ (u v w : V) (huv : Edge (F := F) ρ u v)
    (hvw : Edge (F := F) ρ v w) (huw : Edge (F := F) ρ u w),
    LinearIndepOn F ρ {u,v,w} → (step u v huv).trans (step v w hvw) = step u w huw

variable (hnz : ∀v, ρ v ≠ 0) (C : Frames.ConeSupply (F := F) ρ 5)
variable (o : V)

def connector (v : V) : V := C.pick {o,v}

lemma connector_outside (v : V) :
    ρ (connector ρ C o v) ∉ Submodule.span F (ρ '' ({o,v} : Set V)) := by
  simpa only [connector, Finset.coe_insert, Finset.coe_singleton] using
    C.outside {o,v} (by have h := Finset.card_insert_le o ({v} : Finset V); simp at h; omega)

include hnz

lemma base_connector (v : V) : Edge (F := F) ρ o (connector ρ C o v) :=
  edge_to_cone ρ (by simp) (hnz o) (connector_outside ρ C o v)

lemma vertex_connector (v : V) : Edge (F := F) ρ v (connector ρ C o v) :=
  edge_to_cone ρ (by simp) (hnz v) (connector_outside ρ C o v)

variable {A : V → Type*} (D : FlatSystem (F := F) ρ A)

def canonical (v : V) : A o ≃ A v :=
  (D.step o (connector ρ C o v) (base_connector ρ hnz C o v)).trans
    (D.step (connector ρ C o v) v ((vertex_connector ρ hnz C o v).symm ρ))

lemma canonical_base : canonical ρ hnz C o D o = Equiv.refl (A o) :=
  D.reverse o _ (base_connector ρ hnz C o o)

lemma canonical_to_cone {s : Set V} {v w : V}
    (ho : o ∈ s) (hv : v ∈ s) (hc : connector ρ C o v ∈ s)
    (hw : ρ w ∉ Submodule.span F (ρ '' s)) (a : A o) :
    D.step v w (edge_to_cone ρ hv (hnz v) hw) (canonical ρ hnz C o D v a) =
      D.step o w (edge_to_cone ρ ho (hnz o) hw) a := by
  have ht1 := D.triangle o (connector ρ C o v) w (base_connector ρ hnz C o v)
    (edge_to_cone ρ hc (hnz _) hw) (edge_to_cone ρ ho (hnz o) hw)
    (triangle_to_cone ρ ho hc (base_connector ρ hnz C o v) hw)
  have ht2 := D.triangle (connector ρ C o v) v w ((vertex_connector ρ hnz C o v).symm ρ)
    (edge_to_cone ρ hv (hnz _) hw) (edge_to_cone ρ hc (hnz _) hw)
    (triangle_to_cone ρ hc hv ((vertex_connector ρ hnz C o v).symm ρ) hw)
  have he2 := Equiv.congr_fun ht2 (D.step o _ (base_connector ρ hnz C o v) a)
  have he1 := Equiv.congr_fun ht1 a
  exact he2.trans he1

theorem canonical_edge (u v : V) (huv : Edge (F := F) ρ u v) (a : A o) :
    D.step u v huv (canonical ρ hnz C o D u a) = canonical ρ hnz C o D v a := by
  let s : Finset V := {o,u,v,connector ρ C o u,connector ρ C o v}
  have hs : s.card ≤ 5 := by
    have h₁ := Finset.card_insert_le o ({u,v,connector ρ C o u,connector ρ C o v} : Finset V)
    have h₂ := Finset.card_insert_le u ({v,connector ρ C o u,connector ρ C o v} : Finset V)
    have h₃ := Finset.card_insert_le v ({connector ρ C o u,connector ρ C o v} : Finset V)
    have h₄ := Finset.card_insert_le (connector ρ C o u) ({connector ρ C o v} : Finset V)
    simp only [Finset.card_singleton] at h₄
    dsimp [s]
    omega
  let w := C.pick s
  have hw : ρ w ∉ Submodule.span F (ρ '' (s : Set V)) := C.outside s hs
  have ho : o ∈ (s : Set V) := by simp [s]
  have hu : u ∈ (s : Set V) := by simp [s]
  have hv : v ∈ (s : Set V) := by simp [s]
  have hcu : connector ρ C o u ∈ (s : Set V) := by simp [s]
  have hcv : connector ρ C o v ∈ (s : Set V) := by simp [s]
  apply (D.step v w (edge_to_cone ρ hv (hnz v) hw)).injective
  have ht := D.triangle u v w huv (edge_to_cone ρ hv (hnz v) hw)
    (edge_to_cone ρ hu (hnz u) hw) (triangle_to_cone ρ hu hv huv hw)
  have ht' := Equiv.congr_fun ht (canonical ρ hnz C o D u a)
  exact ht'.trans ((canonical_to_cone ρ hnz C o D ho hu hcu hw a).trans
    (canonical_to_cone ρ hnz C o D ho hv hcv hw a).symm)

include C

theorem unique_section (a : A o) :
    ∃! f : ∀v, A v, f o = a ∧ ∀u v (h : Edge (F := F) ρ u v), D.step u v h (f u) = f v := by
  refine ⟨fun v => canonical ρ hnz C o D v a, ⟨?_, ?_⟩, ?_⟩
  · exact Equiv.congr_fun (canonical_base ρ hnz C o D) a
  · intro u v h
    exact canonical_edge ρ hnz C o D u v h a
  · intro f hf
    funext v
    rw [← hf.2 (connector ρ C o v) v ((vertex_connector ρ hnz C o v).symm ρ),
      ← hf.2 o (connector ρ C o v) (base_connector ρ hnz C o v), hf.1]
    rfl

end
end SourceBurnside.Stability.FrameTransport

end
section
namespace SourceBurnside.Stability.ColumnFrames
noncomputable section
open Classical MatrixGenerators
open scoped Matrix
variable {R ι : Type*} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

def residue (v : ι → R) : ι → ZMod 2 := fun i => ε (v i)
def Vertex := {v : ι → R // residue ε v ≠ 0}
def rho (v : Vertex (ι := ι) ε) : ι → ZMod 2 := residue ε v.val

def standard (i : ι) : Vertex (ι := ι) ε :=
  ⟨Pi.single i 1,by intro hz; have hh := congrFun hz i; simp [residue] at hh⟩

@[simp] lemma rho_standard (i : ι) : rho ε (standard ε i) = (Pi.basisFun (ZMod 2) ι) i := by
  ext j
  by_cases h : j=i <;> simp [rho,standard,residue,h]

lemma standard_injective : Function.Injective (standard (ι := ι) ε) := by
  intro i j h
  have hh := congrArg (rho ε) h
  simpa only [rho_standard] using (Pi.basisFun (ZMod 2) ι).injective (by simpa using hh)

lemma rho_spanning : Submodule.span (ZMod 2) (Set.range (rho (ι := ι) ε)) = ⊤ := by
  apply top_unique
  rw [←(Pi.basisFun (ZMod 2) ι).span_eq]
  apply Submodule.span_mono
  rintro v ⟨i,rfl⟩
  exact ⟨standard ε i,rho_standard ε i⟩

def cones (hι : 5 < Fintype.card ι) : Frames.ConeSupply (F := ZMod 2) (rho (ι := ι) ε) 5 := by
  letI : LinearOrder (Vertex (ι := ι) ε) := linearOrderOfSTO WellOrderingRel
  exact Frames.coneSupply (F := ZMod 2) (rho ε) (rho_spanning ε) 5 (by simpa using hι)

def reduce : (Matrix ι ι R)ˣ →* (Matrix ι ι (ZMod 2))ˣ := Units.map ε.toRingHom.mapMatrix.toMonoidHom

lemma residue_smul (U : (Matrix ι ι R)ˣ) (v : ι → R) :
    residue ε (U • v) = reduce ε U • residue ε v := by
  ext i
  change ε (∑ j, U.val i j * v j) = ∑ j, ε (U.val i j) * ε (v j)
  simp

instance : MulAction (Matrix ι ι R)ˣ (Vertex (ι := ι) ε) where
  smul U v := ⟨U • v.val,by
    rw [residue_smul]
    intro hz
    exact v.property ((MulAction.injective (reduce ε U)) (hz.trans (smul_zero _).symm))⟩
  one_smul v := Subtype.ext (one_smul _ _)
  mul_smul U V v := Subtype.ext (mul_smul U V v.val)

@[simp] lemma smul_val (U : (Matrix ι ι R)ˣ) (v : Vertex (ι := ι) ε) : (U • v).val = U • v.val := rfl
@[simp] lemma rho_smul (U : (Matrix ι ι R)ˣ) (v : Vertex (ι := ι) ε) :
    rho ε (U • v) = reduce ε U • rho ε v := residue_smul ε U v.val

lemma independent_map (U : (Matrix ι ι R)ˣ) {s : Set (Vertex (ι := ι) ε)}
    (hs : LinearIndepOn (ZMod 2) (rho ε) s) :
    LinearIndepOn (ZMod 2) (rho ε) ((fun v => U • v) '' s) := by
  have hh := hs.map_injOn (Matrix.mulVecLin (reduce ε U).val)
    (fun a _ b _ h => (MulAction.injective (reduce ε U)) h)
  have hh' : LinearIndepOn (ZMod 2) (rho ε ∘ fun v => U • v) s :=
    hh.congr (fun v _ => (rho_smul ε U v).symm)
  exact hh'.image_of_comp (fun v => U • v) (rho ε)

lemma edge_map (U : (Matrix ι ι R)ˣ) (u v : Vertex (ι := ι) ε)
    (h : FrameTransport.Edge (F := ZMod 2) (rho ε) u v) : FrameTransport.Edge (F := ZMod 2) (rho ε) (U • u) (U • v) := by
  refine ⟨(MulAction.injective U).ne h.1,?_⟩
  simpa only [Set.image_insert_eq,Set.image_singleton] using independent_map ε U h.2

lemma triangle_map (U : (Matrix ι ι R)ˣ) (u v w : Vertex (ι := ι) ε)
    (h : LinearIndepOn (ZMod 2) (rho ε) {u,v,w}) :
    LinearIndepOn (ZMod 2) (rho ε) {U•u,U•v,U•w} := by
  simpa only [Set.image_insert_eq,Set.image_singleton] using independent_map ε U h

lemma standard_independent (S : Set ι) : LinearIndepOn (ZMod 2) (rho ε) (standard ε '' S) := by
  have hh : LinearIndependent (ZMod 2) (rho ε ∘ standard (ι := ι) ε) := by
    simpa only [Function.comp_def,rho_standard] using (Pi.basisFun (ZMod 2) ι).linearIndependent
  exact (hh.linearIndepOn S).image_of_comp (standard ε) (rho ε)

lemma standard_edge (i j : ι) (h : i≠j) : FrameTransport.Edge (F := ZMod 2) (rho ε) (standard ε i) (standard ε j) := by
  refine ⟨(standard_injective ε).ne h,?_⟩
  simpa only [Set.image_insert_eq, Set.image_singleton] using standard_independent ε ({i,j}:Set ι)

lemma standard_triangle (i j k : ι) :
    LinearIndepOn (ZMod 2) (rho ε) {standard ε i,standard ε j,standard ε k} := by
  simpa only [Set.image_insert_eq, Set.image_singleton] using standard_independent ε ({i,j,k}:Set ι)

@[simp] lemma permutation_standard (p : Equiv.Perm ι) (i : ι) :
    permutation (R := R) p • standard ε i = standard ε (p i) := by
  apply Subtype.ext
  exact permutation_smul_single p i

lemma complete {κ : Type*} (hI : MatrixNilKernel ε.toRingHom) (j : κ ↪ ι)
    (v : κ → Vertex (ι := ι) ε) (hv : LinearIndependent (ZMod 2) (rho ε ∘ v)) :
    ∃U : (Matrix ι ι R)ˣ, ∀k, U • standard ε (j k) = v k := by
  obtain ⟨U,hU⟩ := LinearAlgebra.complete_columns ε hI j (fun k => (v k).val) hv
  refine ⟨U,fun k => ?_⟩
  apply Subtype.ext
  ext i
  change (U.val *ᵥ Pi.single (j k) 1) i = (v k).val i
  simpa using hU k i

end
end SourceBurnside.Stability.ColumnFrames

end
section
namespace SourceBurnside.Stability.ColumnFrames
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
open scoped Matrix
variable {R ι : Type*} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

lemma mem_fixer_iff_standard (S : Finset ι) (U : (Matrix ι ι R)ˣ) :
    U∈fixer S ↔ ∀k∈S, U • standard ε k = standard ε k := by
  simp only [fixer, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]
  constructor
  · intro h k hk
    exact Subtype.ext (h ⟨k,hk⟩)
  · intro h k
    exact congrArg Subtype.val (h k.val k.property)

lemma pair_injective {A : Type*} (a b : A) (hab : a≠b) : Function.Injective ![a,b] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

lemma triple_injective {A : Type*} (a b c : A) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    Function.Injective ![a,b,c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

lemma edge_transitive (hI : MatrixNilKernel ε.toRingHom) (t a : ι) (hta : t≠a)
    (v : Vertex (ι := ι) ε) (hv : FrameTransport.Edge (F := ZMod 2) (rho ε) (standard ε t) v) :
    ∃U : (Matrix ι ι R)ˣ, U∈fixer {t} ∧ U • standard ε a = v := by
  let j : Fin 2 ↪ ι := ⟨![t,a],pair_injective t a hta⟩
  let w : Fin 2 → Vertex (ι := ι) ε := ![standard ε t,v]
  have hw : LinearIndependent (ZMod 2) (rho ε ∘ w) := by
    apply (linearIndepOn_range_iff (pair_injective (standard ε t) v hv.1) (rho ε)).mp
    simpa only [Matrix.range_cons_cons_empty] using hv.2
  obtain ⟨U,hU⟩ := complete ε hI j w hw
  refine ⟨U,?_,?_⟩
  · rw [mem_fixer_iff_standard ε]
    intro k hk
    have hkt : k=t := by simpa using hk
    subst k
    simpa [j,w] using hU 0
  · simpa [j,w] using hU 1

lemma triangle_transitive (hI : MatrixNilKernel ε.toRingHom) (t a b : ι)
    (hta : t≠a) (htb : t≠b) (hab : a≠b) (v w : Vertex (ι := ι) ε)
    (htv : standard ε t ≠ v) (htw : standard ε t ≠ w) (hvw : v≠w)
    (h : LinearIndepOn (ZMod 2) (rho ε) {standard ε t,v,w}) :
    ∃U : (Matrix ι ι R)ˣ, U∈fixer {t} ∧ U • standard ε a=v ∧ U • standard ε b=w := by
  let j : Fin 3 ↪ ι := ⟨![t,a,b],triple_injective t a b hta htb hab⟩
  let f : Fin 3 → Vertex (ι := ι) ε := ![standard ε t,v,w]
  have hf : LinearIndependent (ZMod 2) (rho ε ∘ f) := by
    apply (linearIndepOn_range_iff (triple_injective (standard ε t) v w htv htw hvw) (rho ε)).mp
    simpa [Set.insert_comm,Set.pair_comm] using h
  obtain ⟨U,hU⟩ := complete ε hI j f hf
  refine ⟨U,?_,?_,?_⟩
  · rw [mem_fixer_iff_standard ε]
    intro k hk
    have hkt : k=t := by simpa using hk
    subst k
    simpa [j,f] using hU 0
  · simpa [j,f] using hU 1
  · simpa [j,f] using hU 2

end
end SourceBurnside.Stability.ColumnFrames

end
section
namespace SourceBurnside.Stability.CosetTransport
noncomputable section
open Classical FrameTransport
variable {H V F W : Type*} [Group H] [MulAction H V]
variable [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)

structure Data where
  P : Subgroup H
  o : V
  a : V
  b : V
  s : H
  t : H
  fix : ∀p ∈ P, p • o = o
  sa : s • o = a
  ss : s*s = 1
  sb : s • b = b
  tm : t ∈ P
  ta : t • a = b
  braid : s*t*s = t*s*t
  base : LinearIndepOn F ρ {o,a,b}
  oa : Edge (F := F) ρ o a
  edge_map : ∀(g : H) u v, Edge (F := F) ρ u v → Edge (F := F) ρ (g • u) (g • v)
  tri_map : ∀(g : H) u v w, LinearIndepOn F ρ {u,v,w} → LinearIndepOn F ρ {g•u,g•v,g•w}
  edge_trans : ∀v, Edge (F := F) ρ o v → ∃p ∈ P, p • a = v
  tri_trans : ∀v w, o≠v → o≠w → v≠w → LinearIndepOn F ρ {o,v,w} →
    ∃p ∈ P, p • a = v ∧ p • b = w
  qnorm : ∀p ∈ P, p • a = a → s⁻¹*p*s ∈ P
  generates : Subgroup.closure ((P : Set H) ∪ {s}) = ⊤

variable (D : Data (H := H) (F := F) ρ)

def point : H ⧸ D.P → V := Quotient.lift (fun h : H => h • D.o) (by
  intro h k hk
  have hp := D.fix (h⁻¹*k) ((QuotientGroup.leftRel_apply).mp hk)
  calc h • D.o = h • ((h⁻¹*k) • D.o) := by rw [hp]
       _ = k • D.o := by simp [mul_smul])

@[simp] lemma point_mk (h : H) : point ρ D (QuotientGroup.mk h) = h • D.o := rfl

def Fiber (v : V) := {c : H ⧸ D.P // point ρ D c = v}

def Arrow (x y : H ⧸ D.P) : Prop := ∃h : H,
  QuotientGroup.mk h = x ∧ QuotientGroup.mk (h*D.s) = y

lemma arrow_reverse {x y : H ⧸ D.P} (h : Arrow ρ D x y) : Arrow ρ D y x := by
  obtain ⟨g,rfl,rfl⟩ := h
  refine ⟨g*D.s,rfl,?_⟩
  simp [mul_assoc,D.ss]

lemma arrow_edge {x y : H ⧸ D.P} (h : Arrow ρ D x y) :
    Edge (F := F) ρ (point ρ D x) (point ρ D y) := by
  obtain ⟨g,rfl,rfl⟩ := h
  simpa [mul_smul,D.sa] using D.edge_map g D.o D.a D.oa

lemma arrow_unique {x y z : H ⧸ D.P} (hxy : Arrow ρ D x y) (hxz : Arrow ρ D x z)
    (he : point ρ D y = point ρ D z) : y = z := by
  obtain ⟨g,rfl,rfl⟩ := hxy
  obtain ⟨h,hh,rfl⟩ := hxz
  have hp : g⁻¹*h ∈ D.P := QuotientGroup.eq.mp hh.symm
  have ha : (g⁻¹*h) • D.a = D.a := by
    have eh : g • D.a = h • D.a := by simpa [mul_smul,D.sa] using he
    simpa [mul_smul] using congrArg (fun v => g⁻¹ • v) eh.symm
  apply QuotientGroup.eq.mpr
  simpa [mul_inv_rev,mul_assoc] using D.qnorm _ hp ha

lemma arrow_exists (u v : V) (he : Edge (F := F) ρ u v) (x : Fiber ρ D u) :
    ∃y : Fiber ρ D v, Arrow ρ D x.val y.val := by
  obtain ⟨g,hg⟩ := QuotientGroup.mk_surjective (x.val)
  have hgu : g • D.o = u := by rw [← point_mk ρ D g,hg]; exact x.property
  have hne : Edge (F := F) ρ D.o (g⁻¹ • v) := by
    have hh := D.edge_map g⁻¹ u v he
    simpa [← hgu] using hh
  obtain ⟨p,hp,ep⟩ := D.edge_trans _ hne
  have hy : point ρ D (QuotientGroup.mk (g*p*D.s)) = v := by
    simp only [point_mk,mul_smul,D.sa,ep,smul_inv_smul]
  refine ⟨⟨QuotientGroup.mk (g*p*D.s),hy⟩,g*p,?_,rfl⟩
  rw [QuotientGroup.mk_mul_of_mem g hp,hg]

lemma arrow_triangle {x y z : H ⧸ D.P} (hxy : Arrow ρ D x y) (hyz : Arrow ρ D y z)
    (hn : point ρ D x ≠ point ρ D z)
    (ht : LinearIndepOn F ρ {point ρ D x, point ρ D y, point ρ D z}) :
    Arrow ρ D x z := by
  obtain ⟨g,hg⟩ := QuotientGroup.mk_surjective x
  have htri : LinearIndepOn F ρ {D.o,g⁻¹ • point ρ D y,g⁻¹ • point ρ D z} := by
    have hh := D.tri_map g⁻¹ _ _ _ ht
    simpa [← hg] using hh
  have hxg : g⁻¹ • point ρ D x = D.o := by simp [←hg]
  have h₁ := (MulAction.injective g⁻¹).ne (arrow_edge ρ D hxy).1
  have h₂ := (MulAction.injective g⁻¹).ne hn
  have h₃ := (MulAction.injective g⁻¹).ne (arrow_edge ρ D hyz).1
  rw [hxg] at h₁ h₂
  obtain ⟨p,hp,ha,hb⟩ := D.tri_trans _ _ h₁ h₂ h₃ htri
  let k := g*p
  have hk : QuotientGroup.mk k = x := by dsimp [k]; rw [QuotientGroup.mk_mul_of_mem g hp,hg]
  have hka : k • D.a = point ρ D y := by simp [k,mul_smul,ha]
  have hkb : k • D.b = point ρ D z := by simp [k,mul_smul,hb]
  have hy : QuotientGroup.mk (k*D.s) = y := by
    apply arrow_unique ρ D ⟨k,hk,rfl⟩ hxy
    simpa [point_mk,mul_smul,D.sa] using hka
  have hz : QuotientGroup.mk (k*D.s*D.t*D.s) = z := by
    refine arrow_unique ρ D ⟨k*D.s*D.t,?_,rfl⟩ hyz ?_
    · rw [QuotientGroup.mk_mul_of_mem _ D.tm,hy]
    · simpa [point_mk,mul_smul,D.sa,D.ta,D.sb] using hkb
  have he : QuotientGroup.mk (k*D.s*D.t*D.s) =
      (QuotientGroup.mk (k*D.t*D.s) : H ⧸ D.P) := by
    calc QuotientGroup.mk (k*D.s*D.t*D.s) = QuotientGroup.mk (k*(D.s*D.t*D.s)) := by
           congr 1; group
         _ = QuotientGroup.mk ((k*D.t*D.s)*D.t) := by rw [D.braid]; congr 1; group
         _ = _ := QuotientGroup.mk_mul_of_mem _ D.tm
  refine ⟨k*D.t,?_,he.symm.trans hz⟩
  rw [QuotientGroup.mk_mul_of_mem _ D.tm,hk]

def next (u v : V) (he : Edge (F := F) ρ u v) (x : Fiber ρ D u) : Fiber ρ D v :=
  (arrow_exists ρ D u v he x).choose

lemma next_arrow (u v : V) (he : Edge (F := F) ρ u v) (x : Fiber ρ D u) :
    Arrow ρ D x.val (next ρ D u v he x).val := (arrow_exists ρ D u v he x).choose_spec

lemma next_eq {u v : V} {he : Edge (F := F) ρ u v} {x : Fiber ρ D u} {y : Fiber ρ D v}
    (h : Arrow ρ D x.val y.val) : next ρ D u v he x = y :=
  Subtype.ext (arrow_unique ρ D (next_arrow ρ D u v he x) h
    ((next ρ D u v he x).property.trans y.property.symm))

lemma next_reverse (u v : V) (he : Edge (F := F) ρ u v) (x : Fiber ρ D u) :
    next ρ D v u (he.symm ρ) (next ρ D u v he x) = x :=
  next_eq ρ D (arrow_reverse ρ D (next_arrow ρ D u v he x))

def system : FlatSystem (F := F) ρ (Fiber ρ D) where
  step u v he :=
    { toFun := next ρ D u v he
      invFun := next ρ D v u (he.symm ρ)
      left_inv := next_reverse ρ D u v he
      right_inv := next_reverse ρ D v u (he.symm ρ) }
  reverse u v he := Equiv.ext (next_reverse ρ D u v he)
  triangle u v w huv hvw huw ht := by
    apply Equiv.ext
    intro x
    apply (next_eq ρ D (he := huw) (x := x) (y := next ρ D v w hvw (next ρ D u v huv x)) ?_).symm
    apply arrow_triangle ρ D (next_arrow ρ D u v huv x)
      (next_arrow ρ D v w hvw (next ρ D u v huv x))
    · simpa only [x.property,(next ρ D v w hvw (next ρ D u v huv x)).property] using huw.1
    simpa only [x.property,(next ρ D u v huv x).property,
      (next ρ D v w hvw (next ρ D u v huv x)).property] using ht

theorem point_injective (hnz : ∀v, ρ v ≠ 0) (C : Frames.ConeSupply (F := F) ρ 5) :
    Function.Injective (point ρ D) := by
  let x₀ : Fiber ρ D D.o := ⟨QuotientGroup.mk 1,by simp⟩
  obtain ⟨f,⟨hf₀,hf⟩,_⟩ := unique_section ρ hnz C D.o (system ρ D) x₀
  let ψ : V → H ⧸ D.P := fun v => (f v).val
  have hψ (v : V) : point ρ D (ψ v) = v := (f v).property
  have step_value (u v : V) (he : Edge (F := F) ρ u v) :
      Arrow ρ D (ψ u) (ψ v) := by
    have hh := next_arrow ρ D u v he (f u)
    have heq : next ρ D u v he (f u) = f v := hf u v he
    rw [heq] at hh
    exact hh
  have all (g : H) : QuotientGroup.mk g = ψ (g • D.o) := by
    have hg : g ∈ Subgroup.closure ((D.P : Set H) ∪ {D.s}) := by rw [D.generates]; trivial
    induction hg using Subgroup.closure_induction_right with
    | one => simpa only [one_smul] using (show QuotientGroup.mk 1 = ψ D.o from congrArg Subtype.val hf₀.symm)
    | mul_right g hg k hk ih =>
      rcases hk with hp | hs
      · simpa only [mul_smul,D.fix k hp] using
          (QuotientGroup.mk_mul_of_mem g hp).trans ih
      · obtain rfl := Set.mem_singleton_iff.mp hs
        have he := D.edge_map g D.o D.a D.oa
        have ha : Arrow ρ D (ψ (g • D.o)) (QuotientGroup.mk (g*D.s)) := ⟨g,ih,rfl⟩
        simpa only [mul_smul,D.sa] using (arrow_unique ρ D (step_value _ _ he) ha
          (by simp only [point_mk,hψ,mul_smul,D.sa])).symm
    | mul_inv_cancel g hg k hk ih =>
      rcases hk with hp | hs
      · simpa only [mul_smul,D.fix k⁻¹ (D.P.inv_mem hp)] using
          (QuotientGroup.mk_mul_of_mem g (D.P.inv_mem hp)).trans ih
      · obtain rfl := Set.mem_singleton_iff.mp hs
        have hsi : D.s⁻¹ = D.s := inv_eq_of_mul_eq_one_right D.ss
        rw [hsi]
        have he := D.edge_map g D.o D.a D.oa
        have ha : Arrow ρ D (ψ (g • D.o)) (QuotientGroup.mk (g*D.s)) := ⟨g,ih,rfl⟩
        simpa only [mul_smul,D.sa] using (arrow_unique ρ D (step_value _ _ he) ha
          (by simp only [point_mk,hψ,mul_smul,D.sa])).symm
  intro x y he
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h,rfl⟩ := QuotientGroup.mk_surjective y
  rw [all g,all h]
  exact congrArg ψ he

end
end SourceBurnside.Stability.CosetTransport

end

end OAI
