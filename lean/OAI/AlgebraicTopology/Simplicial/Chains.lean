import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Pi

namespace OAI

noncomputable section

open Classical Set

namespace SimplicialChains
variable {V : Type*}
abbrev Chains (V : Type*) := List V →₀ ℤ

def front (v : V) : Chains V →ₗ[ℤ] Chains V := Finsupp.lmapDomain ℤ ℤ (List.cons v)
@[simp] theorem front_single (v : V) (w : List V) (n : ℤ) :
    front v (Finsupp.single w n) = Finsupp.single (v::w) n := by simp [front]

def boundaryTerm : List V → Chains V
  | [] => 0
  | v::w => Finsupp.single w 1 - front v (boundaryTerm w)
def boundary : Chains V →ₗ[ℤ] Chains V := Finsupp.linearCombination ℤ boundaryTerm
@[simp] theorem boundary_single (w : List V) (n : ℤ) :
    boundary (Finsupp.single w n) = n • boundaryTerm w := by simp [boundary]
@[simp] theorem boundaryTerm_nil : boundaryTerm ([] : List V) = 0 := rfl
@[simp] theorem boundaryTerm_cons (v : V) (w : List V) :
    boundaryTerm (v::w) = Finsupp.single w 1 - front v (boundaryTerm w) := rfl

def includeVec {I : Type*} [Fintype I] (f : I → List V) : (I → ℤ) →ₗ[ℤ] Chains V :=
  (Pi.basisFun ℤ I).constr ℤ (fun i => Finsupp.single (f i) 1)
@[simp] theorem includeVec_single {I : Type*} [Fintype I] [DecidableEq I] (f : I → List V) (i : I) :
    includeVec f (Pi.single i 1) = Finsupp.single (f i) 1 := by
  have hb : (Pi.basisFun ℤ I) i = Pi.single i 1 := by
    funext j
    simp [Pi.basisFun_apply,Pi.single_apply]
  rw [← hb]
  exact (Pi.basisFun ℤ I).constr_basis ℤ _ i

theorem map_ext_single {I M : Type*} [Fintype I] [AddCommGroup M] [Module ℤ M]
    {f g : (I → ℤ) →ₗ[ℤ] M}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply (Pi.basisFun ℤ I).ext
  intro i
  simpa using h i

variable [LinearOrder V] (L : SimpleGraph V)
def Valid (w : List V) : Prop := w.Pairwise (· < ·) ∧ w.Pairwise L.Adj

def chains (k : ℕ) : Submodule ℤ (Chains V) :=
  Finsupp.supported ℤ ℤ {w | Valid L w ∧ w.length = k}

/-- An augmented chain contraction on the actual ordered cliques. -/
structure Contraction where
  homotopy : Chains V →ₗ[ℤ] Chains V
  degree : ∀ k c, c ∈ chains L k → homotopy c ∈ chains L (k+1)
  identity : ∀ w, Valid L w →
    boundary (homotopy (Finsupp.single w 1)) + homotopy (boundaryTerm w) =
      Finsupp.single w 1

variable {L}

theorem valid_sublist {w u : List V} (hw : Valid L w) (hu : u.Sublist w) : Valid L u :=
  ⟨hw.1.sublist hu,hw.2.sublist hu⟩

theorem includeVec_supported {I : Type*} [Fintype I] (f : I → List V) {k : ℕ}
    (hf : ∀ i, Valid L (f i) ∧ (f i).length = k) (c : I → ℤ) :
    includeVec f c ∈ chains L k := by
  have he : ∃ d : I →₀ ℤ, (Pi.basisFun ℤ I).repr.symm d = c :=
    (Pi.basisFun ℤ I).repr.symm.surjective c
  obtain ⟨d,rfl⟩ := he
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa using Submodule.add_mem _ hc hd
  | single i n =>
    have hh : Finsupp.single (f i) (1 : ℤ) ∈ chains L k :=
      Finsupp.single_mem_supported ℤ 1 (hf i)
    have hv : (Pi.basisFun ℤ I).repr.symm (Finsupp.single i n) = n • Pi.single i 1 := by
      simp
    rw [hv,map_smul,includeVec_single]
    exact Submodule.smul_mem _ n hh

/-- Explicit finite index data for vertices, edges and triangles. Every
geometric field is an indexing identity, not an acyclicity assumption. -/
structure TwoDimensionalIndices (E T : Type*) where
  edge : E → V × V
  triangle : T → V × V × V
  face : T → E × E × E
  edgeIndex : V → V → E
  triangleIndex : V → V → V → T
  edge_valid : ∀ e, Valid L [(edge e).1,(edge e).2]
  triangle_valid : ∀ t, Valid L [(triangle t).1,(triangle t).2.1,(triangle t).2.2]
  edge_inverse : ∀ e, edgeIndex (edge e).1 (edge e).2 = e
  edge_complete : ∀ a b, Valid L [a,b] → edge (edgeIndex a b) = (a,b)
  triangle_complete : ∀ a b c, Valid L [a,b,c] → triangle (triangleIndex a b c) = (a,b,c)
  face_edge : ∀ t,
    edge (face t).1 = ((triangle t).2.1,(triangle t).2.2) ∧
    edge (face t).2.1 = ((triangle t).1,(triangle t).2.2) ∧
    edge (face t).2.2 = ((triangle t).1,(triangle t).2.1)
  length_le : ∀ w, Valid L w → w.length ≤ 3

namespace TwoDimensionalIndices
variable {E T : Type*} [Fintype V] [Fintype E] [Fintype T]
variable (D : TwoDimensionalIndices (L := L) E T)
def vList (v : V) : List V := [v]
def eList (e : E) : List V := [(D.edge e).1,(D.edge e).2]
def tList (t : T) : List V := [(D.triangle t).1,(D.triangle t).2.1,(D.triangle t).2.2]

variable (root : V) (h₀ : (V → ℤ) →ₗ[ℤ] (E → ℤ))
    (h₁ : (E → ℤ) →ₗ[ℤ] (T → ℤ))

def fillTerm : List V → Chains V
  | [] => Finsupp.single [root] 1
  | [v] => includeVec D.eList (h₀ (Pi.single v 1))
  | [a,b] => includeVec D.tList (h₁ (Pi.single (D.edgeIndex a b) 1))
  | _ => 0

def fill : Chains V →ₗ[ℤ] Chains V := Finsupp.linearCombination ℤ (D.fillTerm root h₀ h₁)
omit [Fintype V] in
@[simp] theorem fill_single (w : List V) (n : ℤ) :
    D.fill root h₀ h₁ (Finsupp.single w n) = n • D.fillTerm root h₀ h₁ w := by simp [fill]

theorem fill_include_vertex (c : V → ℤ) :
    D.fill root h₀ h₁ (includeVec vList c) = includeVec D.eList (h₀ c) := by
  have hh : (D.fill root h₀ h₁).comp (includeVec vList) = (includeVec D.eList).comp h₀ := by
    apply map_ext_single
    intro i
    simp [fillTerm,vList]
    congr 2
    funext v
    simp [Pi.single_apply]
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
theorem fill_include_edge (c : E → ℤ) :
    D.fill root h₀ h₁ (includeVec D.eList c) = includeVec D.tList (h₁ c) := by
  have hh : (D.fill root h₀ h₁).comp (includeVec D.eList) = (includeVec D.tList).comp h₁ := by
    apply map_ext_single
    intro i
    simp [fillTerm,eList,D.edge_inverse]
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
theorem fill_include_triangle (c : T → ℤ) :
    D.fill root h₀ h₁ (includeVec D.tList c) = 0 := by
  have hh : (D.fill root h₀ h₁).comp (includeVec D.tList) = 0 := by
    apply map_ext_single
    intro i
    simp [fillTerm,tList]
  exact LinearMap.congr_fun hh c

variable (d₁ : (E → ℤ) →ₗ[ℤ] (V → ℤ)) (d₂ : (T → ℤ) →ₗ[ℤ] (E → ℤ))
    (hd₁ : ∀ e, d₁ (Pi.single e 1) = Pi.single (D.edge e).2 1 - Pi.single (D.edge e).1 1)
    (hd₂ : ∀ t, d₂ (Pi.single t 1) = Pi.single (D.face t).1 1 -
      Pi.single (D.face t).2.1 1 + Pi.single (D.face t).2.2 1)

omit [Fintype T] in
include hd₁ in
theorem boundary_include_edge (c : E → ℤ) :
    boundary (includeVec D.eList c) = includeVec vList (d₁ c) := by
  have hh : boundary.comp (includeVec D.eList) = (includeVec vList).comp d₁ := by
    apply map_ext_single
    intro e
    simp [hd₁,eList,vList]
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
include hd₂ in
theorem boundary_include_triangle (c : T → ℤ) :
    boundary (includeVec D.tList c) = includeVec D.eList (d₂ c) := by
  have hh : boundary.comp (includeVec D.tList) = (includeVec D.eList).comp d₂ := by
    apply map_ext_single
    intro t
    obtain ⟨h₁,h₂,h₃⟩ := D.face_edge t
    simp [hd₂,tList,eList,h₁,h₂,h₃,map_sub]
    abel
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
theorem fill_degree (k : ℕ) (c : Chains V) (hc : c ∈ chains L k) :
    D.fill root h₀ h₁ c ∈ chains L (k+1) := by
  rw [chains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => D.fill root h₀ h₁ c ∈ chains L (k+1)) _ _ _ _ hc
  · rintro _ ⟨w,⟨hw,hl⟩,rfl⟩
    simp only [fill_single,one_smul]
    subst k
    rcases w with _ | ⟨a,w⟩
    · exact Finsupp.single_mem_supported ℤ 1 (by simp [Valid])
    rcases w with _ | ⟨b,w⟩
    · exact includeVec_supported D.eList (fun e => ⟨D.edge_valid e,rfl⟩) _
    rcases w with _ | ⟨d,w⟩
    · exact includeVec_supported D.tList (fun t => ⟨D.triangle_valid t,rfl⟩) _
    · exact Submodule.zero_mem _
  · simp
  · intro c d _ _ hc hd
    simpa using Submodule.add_mem _ hc hd
  · intro n c _ hc
    simpa using Submodule.smul_mem _ n hc

variable (hbottom : ∀ v, d₁ (h₀ (Pi.single v 1)) = Pi.single v 1 - Pi.single root 1)
    (hleft : ∀ t, h₁ (d₂ (Pi.single t 1)) = Pi.single t 1)
    (hmiddle : ∀ e, d₂ (h₁ (Pi.single e 1)) + h₀ (d₁ (Pi.single e 1)) = Pi.single e 1)

include hd₁ hbottom in
 theorem vertex_identity (v : V) :
    boundary (D.fill root h₀ h₁ (Finsupp.single [v] 1)) +
      D.fill root h₀ h₁ (boundaryTerm [v]) = Finsupp.single [v] 1 := by
  simp only [fill_single,one_smul,fillTerm]
  rw [D.boundary_include_edge d₁ hd₁,hbottom]
  simp [fillTerm,vList]

include hd₁ hd₂ hmiddle in
 theorem edge_identity (e : E) :
    boundary (D.fill root h₀ h₁ (Finsupp.single (D.eList e) 1)) +
      D.fill root h₀ h₁ (boundaryTerm (D.eList e)) = Finsupp.single (D.eList e) 1 := by
  calc
    _ = boundary (D.fill root h₀ h₁ (includeVec D.eList (Pi.single e 1))) +
        D.fill root h₀ h₁ (boundary (includeVec D.eList (Pi.single e 1))) := by simp
    _ = includeVec D.eList (d₂ (h₁ (Pi.single e 1))) +
        includeVec D.eList (h₀ (d₁ (Pi.single e 1))) := by
      rw [D.fill_include_edge,D.boundary_include_triangle d₂ hd₂,
        D.boundary_include_edge d₁ hd₁,D.fill_include_vertex]
    _ = _ := by rw [← map_add,hmiddle,includeVec_single]

omit [Fintype V] in
include hd₂ hleft in
 theorem triangle_identity (t : T) :
    boundary (D.fill root h₀ h₁ (Finsupp.single (D.tList t) 1)) +
      D.fill root h₀ h₁ (boundaryTerm (D.tList t)) = Finsupp.single (D.tList t) 1 := by
  calc
    _ = boundary (D.fill root h₀ h₁ (includeVec D.tList (Pi.single t 1))) +
        D.fill root h₀ h₁ (boundary (includeVec D.tList (Pi.single t 1))) := by simp
    _ = includeVec D.tList (h₁ (d₂ (Pi.single t 1))) := by
      rw [D.fill_include_triangle,map_zero,zero_add,
        D.boundary_include_triangle d₂ hd₂,D.fill_include_edge]
    _ = _ := by rw [hleft,includeVec_single]

/-- All finite matrix certificate equations are used to obtain a genuine
augmented contraction of every actual clique of the graph. -/
def contraction : Contraction L where
  homotopy := D.fill root h₀ h₁
  degree := D.fill_degree root h₀ h₁
  identity := by
    intro w hw
    have hl := D.length_le w hw
    rcases w with _ | ⟨a,w⟩
    · simp [fillTerm]
    rcases w with _ | ⟨b,w⟩
    · exact D.vertex_identity root h₀ h₁ d₁ hd₁ hbottom a
    rcases w with _ | ⟨c,w⟩
    · have he : D.eList (D.edgeIndex a b) = [a,b] := by
        simp [eList,D.edge_complete a b hw]
      rw [← he]
      exact D.edge_identity root h₀ h₁ d₁ d₂ hd₁ hd₂ hmiddle _
    have hw' : w = [] := by
      have hh : w.length = 0 := by simp only [List.length_cons] at hl; omega
      exact List.length_eq_zero_iff.mp hh
    subst w
    have he : D.tList (D.triangleIndex a b c) = [a,b,c] := by
      simp [tList,D.triangle_complete a b c hw]
    rw [← he]
    exact D.triangle_identity root h₀ h₁ d₂ hd₂ hleft _

end TwoDimensionalIndices
end SimplicialChains



namespace SimplicialChains
variable {V W : Type*}
def reindex (f : V → W) : Chains V →ₗ[ℤ] Chains W :=
  Finsupp.lmapDomain ℤ ℤ (List.map f)
@[simp] theorem reindex_single (f : V → W) (w : List V) (n : ℤ) :
    reindex f (Finsupp.single w n) = Finsupp.single (w.map f) n := by simp [reindex]
@[simp] theorem reindex_front (f : V → W) (v : V) (c : Chains V) :
    reindex f (front v c) = front (f v) (reindex f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single w n => simp

theorem reindex_boundaryTerm (f : V → W) (w : List V) :
    reindex f (boundaryTerm w) = boundaryTerm (w.map f) := by
  induction w with
  | nil => simp
  | cons v w ih => simp only [boundaryTerm_cons,map_sub,reindex_single,reindex_front,ih,List.map_cons]

theorem reindex_boundary (f : V → W) (c : Chains V) :
    reindex f (boundary c) = boundary (reindex f c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single w n => simp [reindex_boundaryTerm]

@[simp] theorem reindex_inverse (e : V ≃ W) (c : Chains V) :
    reindex e.symm (reindex e c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add,hc,hd]
  | single w n => simp

variable [LinearOrder V] [LinearOrder W] {L : SimpleGraph V} {M : SimpleGraph W}
theorem reindex_degree (f : V → W) (hf : ∀ w, Valid L w → Valid M (w.map f))
    {k : ℕ} {c : Chains V} (hc : c ∈ chains L k) : reindex f c ∈ chains M k := by
  rw [chains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => reindex f c ∈ chains M k) _ _ _ _ hc
  · rintro _ ⟨w,⟨hw,hl⟩,rfl⟩
    rw [reindex_single]
    exact Finsupp.single_mem_supported ℤ 1 ⟨hf w hw,by simpa using hl⟩
  · simp
  · intro c d _ _ hc hd; simpa only [map_add] using (chains M k).add_mem hc hd
  · intro n c _ hc; simpa only [map_smul] using (chains M k).smul_mem n hc

/-- Transport a genuine augmented contraction along a graph/order reindexing. -/
def Contraction.reindex (K : Contraction L) (e : V ≃ W)
    (hf : ∀ w, Valid L w → Valid M (w.map e))
    (hb : ∀ w, Valid M w → Valid L (w.map e.symm)) : Contraction M where
  homotopy := (SimplicialChains.reindex e).comp (K.homotopy.comp (SimplicialChains.reindex e.symm))
  degree := by
    intro k c hc
    exact reindex_degree e hf (K.degree k _ (reindex_degree e.symm hb hc))
  identity := by
    intro w hw
    have hh := congrArg (SimplicialChains.reindex e) (K.identity (w.map e.symm) (hb w hw))
    simp only [map_add,reindex_boundary,← reindex_boundaryTerm] at hh
    simpa only [LinearMap.comp_apply,reindex_single,List.map_map,Equiv.apply_symm_apply,
      Function.comp_def,List.map_id_fun',id_eq] using hh
end SimplicialChains



end

end OAI
