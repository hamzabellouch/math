import OAI.Analysis.InterpolatedFactors.Diffuse

namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
namespace FreeGroupFactorMain
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def algebraCyclic (A : StarSubalgebra ℂ (E →L[ℂ] E)) (ξ : E) : Submodule ℂ E where
  carrier := {η | ∃ T ∈ A, T ξ=η}
  zero_mem' := ⟨0,A.zero_mem,rfl⟩
  add_mem' := by
    rintro x y ⟨S,hS,rfl⟩ ⟨T,hT,rfl⟩
    exact ⟨S+T,A.add_mem hS hT,rfl⟩
  smul_mem' := by
    rintro c x ⟨T,hT,rfl⟩
    exact ⟨c • T,A.smul_mem hT c,rfl⟩

 theorem algebraCyclic_invariant (A : StarSubalgebra ℂ (E →L[ℂ] E)) (ξ : E)
    (T : E →L[ℂ] E) (hT : T ∈ A) {η : E} (hη : η ∈ algebraCyclic A ξ) :
    T η ∈ algebraCyclic A ξ := by
  obtain ⟨S,hS,rfl⟩ := hη
  exact ⟨T*S,A.mul_mem hT hS,rfl⟩

 theorem algebraCyclic_closure_invariant (A : StarSubalgebra ℂ (E →L[ℂ] E)) (ξ : E)
    (T : E →L[ℂ] E) (hT : T ∈ A) {η : E} (hη : η ∈ (algebraCyclic A ξ).topologicalClosure) :
    T η ∈ (algebraCyclic A ξ).topologicalClosure := by
  exact closure_minimal (t := {x : E | T x ∈ (algebraCyclic A ξ).topologicalClosure})
    (fun x hx => (algebraCyclic A ξ).le_topologicalClosure (algebraCyclic_invariant A ξ T hT hx))
    ((algebraCyclic A ξ).isClosed_topologicalClosure.preimage T.continuous) hη

 theorem projection_commutes_of_invariant (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (T : E →L[ℂ] E) (hT : ∀ η ∈ K, T η ∈ K)
    (hTs : ∀ η ∈ K, (star T) η ∈ K) : Commute K.starProjection T := by
  apply ContinuousLinearMap.ext
  intro η
  change K.starProjection (T η)=T (K.starProjection η)
  apply K.eq_starProjection_of_mem_of_inner_eq_zero (hT _ (K.starProjection_apply_mem η))
  intro z hz
  rw [← map_sub,← ContinuousLinearMap.adjoint_inner_right]
  exact K.starProjection_inner_eq_zero η _ (hTs _ hz)

 theorem bicommutant_vector_mem_cyclic (S : Set (E →L[ℂ] E)) (ξ : E)
    (T : E →L[ℂ] E)
    (hT : T ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ S : Set (E →L[ℂ] E))) :
    T ξ ∈ (algebraCyclic (StarAlgebra.adjoin ℂ S) ξ).topologicalClosure := by
  let A := StarAlgebra.adjoin ℂ S
  let K := (algebraCyclic A ξ).topologicalClosure
  have hP : K.starProjection ∈ StarSubalgebra.centralizer ℂ S := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro U hU
    have hUa : U ∈ A := StarAlgebra.subset_adjoin ℂ S hU
    have hc (V : E →L[ℂ] E) (hV : V ∈ A) : Commute K.starProjection V :=
      projection_commutes_of_invariant K V
        (fun _ h => algebraCyclic_closure_invariant A ξ V hV h)
        (fun _ h => algebraCyclic_closure_invariant A ξ (star V) (star_mem hV) h)
    exact ⟨(hc U hUa).eq.symm,(hc (star U) (star_mem hUa)).eq.symm⟩
  have hξ : ξ ∈ K := (algebraCyclic A ξ).le_topologicalClosure ⟨1,A.one_mem,rfl⟩
  have hc := DFunLike.congr_fun (((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hP).1) ξ
  change K.starProjection (T ξ)=T (K.starProjection ξ) at hc
  rw [K.starProjection_eq_self_iff.mpr hξ] at hc
  exact K.starProjection_eq_self_iff.mp hc
end FreeGroupFactorMain
namespace FreeGroupFactorMain.PairCyclic

section
variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
local notation "Pair" => WithLp 2 (E × E)
local notation "Op" => (E →L[ℂ] E)

def diag (T : Op) : Pair →L[ℂ] Pair :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap ∘L
    T.prodMap T ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ E E).toContinuousLinearMap

theorem diag_apply (T : Op) (x : Pair) : diag T x=WithLp.toLp 2 (T x.fst,T x.snd) := rfl

theorem diag_star [CompleteSpace E] (T : Op) : star (diag T)=diag (star T) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [diag_apply,WithLp.prod_inner_apply,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  rfl

def coord (i : Bool) : Pair →L[ℂ] E :=
  if i then WithLp.sndL 2 ℂ E E else WithLp.fstL 2 ℂ E E

def embed (i : Bool) : E →L[ℂ] Pair :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap ∘L
    (if i then ContinuousLinearMap.inr ℂ E E else ContinuousLinearMap.inl ℂ E E)

theorem coord_diag (i : Bool) (T : Op) (x : Pair) : coord i (diag T x)=T (coord i x) := by
  cases i <;> rfl

theorem diag_embed (i : Bool) (T : Op) (x : E) : diag T (embed i x)=embed i (T x) := by
  cases i <;> apply (WithLp.prodContinuousLinearEquiv 2 ℂ E E).injective <;>
    simp [diag,embed,ContinuousLinearMap.prodMap]

theorem pair_decompose (x : Pair) : x=embed false (coord false x)+embed true (coord true x) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ E E).injective
  simp [embed,coord]
  rfl

def block (Q : Pair →L[ℂ] Pair) (i j : Bool) : Op := coord i ∘L Q ∘L embed j

theorem block_commute {Q : Pair →L[ℂ] Pair} {T : Op} (h : Commute Q (diag T)) (i j : Bool) :
    Commute (block Q i j) T := by
  ext x
  have hh := congrArg (fun y : Pair => coord i y) (DFunLike.congr_fun h.eq (embed j x))
  simpa only [mul_apply_eq_comp,diag_embed,coord_diag,block,ContinuousLinearMap.comp_apply] using hh

theorem diag_commute_of_blocks {Q : Pair →L[ℂ] Pair} {T : Op}
    (h : ∀ i j, Commute (block Q i j) T) : Commute Q (diag T) := by
  ext x
  have hc (i : Bool) : coord i (Q (diag T x))=coord i (diag T (Q x)) := by
    have hh (j : Bool) := DFunLike.congr_fun (h i j).eq (coord j x)
    simp only [mul_apply_eq_comp,block,ContinuousLinearMap.comp_apply] at hh
    rw [coord_diag, pair_decompose x, map_add,map_add,map_add,map_add,diag_embed,diag_embed,
      hh false,hh true]
    simp only [map_add]
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ E E).injective
  exact Prod.ext (hc false) (hc true)

variable [CompleteSpace E]

def orbit (A : StarSubalgebra ℂ Op) (x : Pair) : Submodule ℂ Pair where
  carrier := {y | ∃ T∈A,diag T x=y}
  zero_mem' := ⟨0,A.zero_mem,by apply (WithLp.prodContinuousLinearEquiv 2 ℂ E E).injective; rfl⟩
  add_mem' := by
    rintro y z ⟨S,hS,rfl⟩ ⟨T,hT,rfl⟩
    exact ⟨S+T,add_mem hS hT,rfl⟩
  smul_mem' := by
    rintro c y ⟨T,hT,rfl⟩
    exact ⟨c • T,A.smul_mem hT c,rfl⟩

theorem orbit_invariant (A : StarSubalgebra ℂ Op) (x : Pair) (T : Op) (hT : T∈A)
    {y : Pair} (hy : y∈orbit A x) : diag T y∈orbit A x := by
  obtain ⟨S,hS,rfl⟩ := hy
  exact ⟨T*S,mul_mem hT hS,rfl⟩

theorem closure_invariant (A : StarSubalgebra ℂ Op) (x : Pair) (T : Op) (hT : T∈A)
    {y : Pair} (hy : y∈(orbit A x).topologicalClosure) : diag T y∈(orbit A x).topologicalClosure := by
  exact closure_minimal (t := {y : Pair | diag T y∈(orbit A x).topologicalClosure})
    (fun y hy => (orbit A x).le_topologicalClosure (orbit_invariant A x T hT hy))
    ((orbit A x).isClosed_topologicalClosure.preimage (diag T).continuous) hy

theorem bicommutant_mem_closure (S : Set Op) (x : Pair) (T : Op)
    (hT : T∈StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set Op)) :
    diag T x∈(orbit (StarAlgebra.adjoin ℂ S) x).topologicalClosure := by
  let A := StarAlgebra.adjoin ℂ S
  let K := (orbit A x).topologicalClosure
  have hc (U : Op) (hU : U∈A) : Commute K.starProjection (diag U) :=
    projection_commutes_of_invariant K (diag U)
      (fun _ hy => closure_invariant A x U hU hy)
      (fun y hy => by rw [diag_star]; exact closure_invariant A x (star U) (star_mem hU) hy)
  have hb (i j : Bool) : block K.starProjection i j∈StarSubalgebra.centralizer ℂ S := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro U hU
    have hUa : U∈A := StarAlgebra.subset_adjoin ℂ S hU
    exact ⟨(block_commute (hc U hUa) i j).symm.eq,
      (block_commute (hc (star U) (star_mem hUa)) i j).symm.eq⟩
  have hcomm : Commute K.starProjection (diag T) := diag_commute_of_blocks (fun i j =>
    (((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ (hb i j)).1))
  have hx : x∈K := (orbit A x).le_topologicalClosure ⟨1,A.one_mem,rfl⟩
  have he := DFunLike.congr_fun hcomm.eq x
  change K.starProjection (diag T x)=diag T (K.starProjection x) at he
  rw [K.starProjection_eq_self_iff.mpr hx] at he
  exact K.starProjection_eq_self_iff.mp he

end
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local notation "Pair" => WithLp 2 (E × E)
local notation "Op" => (E →L[ℂ] E)

theorem invariant_bicommutant (S : Set Op) (K : Submodule ℂ Pair) [K.HasOrthogonalProjection]
    (hS : ∀ U∈S, ∀ y∈K, diag U y∈K)
    (hSs : ∀ U∈S, ∀ y∈K, diag (star U) y∈K)
    (T : Op) (hT : T∈StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set Op))
    (x : Pair) (hx : x∈K) : diag T x∈K := by
  have hc (U : Op) (hU : U∈S) : Commute K.starProjection (diag U) :=
    projection_commutes_of_invariant K (diag U) (hS U hU)
      (fun y hy => by rw [diag_star]; exact hSs U hU y hy)
  have hcs (U : Op) (hU : U∈S) : Commute K.starProjection (diag (star U)) := by
    have hs := (hc U hU).star_star
    simpa only [(isSelfAdjoint_starProjection K).star_eq,diag_star] using hs
  have hb (i j : Bool) : block K.starProjection i j∈StarSubalgebra.centralizer ℂ S := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro U hU
    exact ⟨(block_commute (hc U hU) i j).symm.eq,(block_commute (hcs U hU) i j).symm.eq⟩
  have hcomm := diag_commute_of_blocks (fun i j =>
    (((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ (hb i j)).1))
  have he := DFunLike.congr_fun hcomm.eq x
  change K.starProjection (diag T x)=diag T (K.starProjection x) at he
  rw [K.starProjection_eq_self_iff.mpr hx] at he
  exact K.starProjection_eq_self_iff.mp he
end FreeGroupFactorMain.PairCyclic
namespace FreeGroupFactorMain.GaussianExtension

section
variable {E : Type u_4} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local notation "Pair" => WithLp 2 (E × E)
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (D : E →L[ℂ] E)

def creationWord (ξ : E) (a : B) (w : List B) : E :=
  (a : (E →L[ℂ] E)) (w.foldr (fun b y => D ((b : (E →L[ℂ] E)) y)) ξ)

def pairNormal (ξ η : E) (w : B × List B) : Pair :=
  WithLp.toLp 2 (creationWord B D ξ w.1 w.2,creationWord B D η w.1 w.2)

def creationWordSpan (ξ η : E) : Submodule ℂ Pair :=
  Submodule.span ℂ (Set.range (pairNormal B D ξ η))

theorem creationWord_coeff (ξ : E) (a b : B) (w : List B) :
    (a : (E →L[ℂ] E)) (creationWord B D ξ b w)=creationWord B D ξ (a*b) w := by
  cases w <;> rfl

theorem creationWord_create (ξ : E) (a : B) (w : List B) :
    D (creationWord B D ξ a w)=creationWord B D ξ 1 (a::w) := rfl

variable (κ : B → B) (hκ : ∀ a : B,star D*(a : (E →L[ℂ] E))*D=(κ a : (E →L[ℂ] E)))

theorem creationWord_annihilate_nil (ξ : E) (hξ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ξ)=0) (a : B) :
    star D (creationWord B D ξ a [])=0 := hξ a

include hκ in
theorem creationWord_annihilate_cons (ξ : E) (a b : B) (w : List B) :
    star D (creationWord B D ξ a (b::w))=creationWord B D ξ (κ a*b) w := by
  have hh := DFunLike.congr_fun (hκ a) (creationWord B D ξ b w)
  exact hh

theorem pairNormal_coeff (ξ η : E) (a : B) (w : B × List B) :
    PairCyclic.diag (a : (E →L[ℂ] E)) (pairNormal B D ξ η w)=pairNormal B D ξ η (a*w.1,w.2) := by
  simp only [pairNormal,PairCyclic.diag_apply,WithLp.toLp_fst,WithLp.toLp_snd,creationWord_coeff]

theorem pairNormal_create (ξ η : E) (w : B × List B) :
    PairCyclic.diag D (pairNormal B D ξ η w)=pairNormal B D ξ η (1,w.1::w.2) := by
  simp only [pairNormal,PairCyclic.diag_apply,WithLp.toLp_fst,WithLp.toLp_snd,creationWord_create]

include hκ in
theorem pairNormal_semicircle_mem (ξ η : E)
    (hξ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ξ)=0) (hη : ∀ a : B,star D ((a : (E →L[ℂ] E)) η)=0)
    (w : B × List B) : PairCyclic.diag (D+star D) (pairNormal B D ξ η w)∈creationWordSpan B D ξ η := by
  have hcreate : PairCyclic.diag D (pairNormal B D ξ η w)∈creationWordSpan B D ξ η := by
    rw [pairNormal_create]
    exact Submodule.subset_span (Set.mem_range_self _)
  have hann : PairCyclic.diag (star D) (pairNormal B D ξ η w)∈creationWordSpan B D ξ η := by
    rcases w with ⟨a,w⟩
    cases w with
    | nil =>
      have hz : PairCyclic.diag (star D) (pairNormal B D ξ η (a,[]))=0 := by
        simp only [pairNormal,PairCyclic.diag_apply,WithLp.toLp_fst,WithLp.toLp_snd,
          creationWord_annihilate_nil B D ξ hξ,creationWord_annihilate_nil B D η hη]
        rfl
      rw [hz]
      exact (creationWordSpan B D ξ η).zero_mem
    | cons b w =>
      have he : PairCyclic.diag (star D) (pairNormal B D ξ η (a,b::w))=
          pairNormal B D ξ η (κ a*b,w) := by
        simp only [pairNormal,PairCyclic.diag_apply,WithLp.toLp_fst,WithLp.toLp_snd,
          creationWord_annihilate_cons B D κ hκ]
      rw [he]
      exact Submodule.subset_span (Set.mem_range_self _)
  exact (creationWordSpan B D ξ η).add_mem hcreate hann

theorem span_invariant_of_family (ξ η : E) (T : (E →L[ℂ] E))
    (hT : ∀ w,PairCyclic.diag T (pairNormal B D ξ η w)∈creationWordSpan B D ξ η)
    (z : Pair) (hz : z∈creationWordSpan B D ξ η) : PairCyclic.diag T z∈creationWordSpan B D ξ η := by
  have hh : creationWordSpan B D ξ η≤(creationWordSpan B D ξ η).comap (PairCyclic.diag T).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    exact hT w
  exact hh hz

theorem closure_invariant_of_family (ξ η : E) (T : (E →L[ℂ] E))
    (hT : ∀ w,PairCyclic.diag T (pairNormal B D ξ η w)∈creationWordSpan B D ξ η)
    (z : Pair) (hz : z∈(creationWordSpan B D ξ η).topologicalClosure) :
    PairCyclic.diag T z∈(creationWordSpan B D ξ η).topologicalClosure := by
  exact closure_minimal (t := {z : Pair | PairCyclic.diag T z∈(creationWordSpan B D ξ η).topologicalClosure})
    (fun z hz => (creationWordSpan B D ξ η).le_topologicalClosure (span_invariant_of_family B D ξ η T hT z hz))
    ((creationWordSpan B D ξ η).isClosed_topologicalClosure.preimage (PairCyclic.diag T).continuous) hz

include hκ in
theorem bicommutant_pair_creationWord (ξ η : E)
    (hξ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ξ)=0) (hη : ∀ a : B,star D ((a : (E →L[ℂ] E)) η)=0)
    (T : (E →L[ℂ] E))
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert (D+star D) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))) :
    PairCyclic.diag T (WithLp.toLp 2 (ξ,η))∈(creationWordSpan B D ξ η).topologicalClosure := by
  have hS (U : (E →L[ℂ] E)) (hU : U∈insert (D+star D) (B : Set (E →L[ℂ] E))) :
      ∀ z∈(creationWordSpan B D ξ η).topologicalClosure,
      PairCyclic.diag U z∈(creationWordSpan B D ξ η).topologicalClosure := by
    apply closure_invariant_of_family B D ξ η U
    intro w
    rcases hU with rfl|hU
    · exact pairNormal_semicircle_mem B D κ hκ ξ η hξ hη w
    · rw [pairNormal_coeff B D ξ η ⟨U,hU⟩]
      exact Submodule.subset_span (Set.mem_range_self _)
  have hSs (U : (E →L[ℂ] E)) (hU : U∈insert (D+star D) (B : Set (E →L[ℂ] E))) :
      star U∈insert (D+star D) (B : Set (E →L[ℂ] E)) := by
    rcases hU with rfl|hU
    · rw [(IsSelfAdjoint.add_star_self D).star_eq]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (star_mem hU)
  apply PairCyclic.invariant_bicommutant _ (creationWordSpan B D ξ η).topologicalClosure hS
    (fun U hU => hS (star U) (hSs U hU)) T hT
  apply (creationWordSpan B D ξ η).le_topologicalClosure
  exact Submodule.subset_span ⟨(1,[]),rfl⟩

def constraint (ξ : E) (L : (E →L[ℂ] E)) (z : E) : Pair →L[ℂ] E :=
  (star L) ∘L WithLp.fstL 2 ℂ E E-
    (ContinuousLinearMap.toSpanSingleton ℂ z) ∘L (innerSL ℂ ξ) ∘L WithLp.sndL 2 ℂ E E

theorem constraint_apply (ξ : E) (L : (E →L[ℂ] E)) (z : E) (x : Pair) :
    constraint ξ L z x=star L x.fst-(inner ℂ ξ x.snd) • z := rfl

include hκ in

theorem covariance_extension (L R Q : (E →L[ℂ] E)) (ξ ζ : E)
    (hξ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ξ)=0)
    (hζ : ∀ a : B,star D ((a : (E →L[ℂ] E)) ζ)=0)
    (hL : ∀ a : B,star L*(a : (E →L[ℂ] E))*D=0)
    (hR : ∀ a : B,star D*(a : (E →L[ℂ] E))*R=0)
    (hbase : ∀ a : B,star L*(a : (E →L[ℂ] E))*R=(inner ℂ ξ ((a : (E →L[ℂ] E)) ζ)) • Q)
    (T : (E →L[ℂ] E))
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert (D+star D) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))) :
    star L*T*R=(inner ℂ ξ (T ζ)) • Q := by
  ext η
  let F := constraint ξ L (Q η)
  have hroot : ∀ a : B,star D ((a : (E →L[ℂ] E)) (R η))=0 := by
    intro a
    have hh := DFunLike.congr_fun (hR a) η
    exact hh
  have hfamily (w : B × List B) : F (pairNormal B D (R η) ζ w)=0 := by
    rcases w with ⟨a,w⟩
    cases w with
    | nil =>
      have hh := DFunLike.congr_fun (hbase a) η
      change star L ((a : (E →L[ℂ] E)) (R η))=(inner ℂ ξ ((a : (E →L[ℂ] E)) ζ)) • (Q η) at hh
      change star L ((a : (E →L[ℂ] E)) (R η))-(inner ℂ ξ ((a : (E →L[ℂ] E)) ζ)) • (Q η)=0
      exact sub_eq_zero.mpr hh
    | cons b w =>
      have hz : star L ((a : (E →L[ℂ] E)) (D (creationWord B D (R η) b w)))=0 :=
        DFunLike.congr_fun (hL a) _
      have hi : inner ℂ ξ ((a : (E →L[ℂ] E)) (D (creationWord B D ζ b w)))=0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.adjoint_inner_left]
        change inner ℂ (star D (((star a : B) : (E →L[ℂ] E)) ξ)) _=0
        rw [hξ (star a),inner_zero_left]
      change star L ((a : (E →L[ℂ] E)) (D (creationWord B D (R η) b w)))-
        (inner ℂ ξ ((a : (E →L[ℂ] E)) (D (creationWord B D ζ b w)))) • (Q η)=0
      rw [hz,hi,zero_smul,sub_self]
  have hspan : creationWordSpan B D (R η) ζ≤LinearMap.ker F.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w,rfl⟩
    exact hfamily w
  have hclosure := (creationWordSpan B D (R η) ζ).topologicalClosure_minimal hspan
    F.isClosed_ker
  have hh := hclosure (bicommutant_pair_creationWord B D κ hκ (R η) ζ hroot hζ T hT)
  change star L (T (R η))-(inner ℂ ξ (T ζ)) • (Q η)=0 at hh
  exact sub_eq_zero.mp hh

end
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (D : E →L[ℂ] E)
variable (κ : B → B) (hκ : ∀ a : B,star D*(a : E →L[ℂ] E)*D=(κ a : E →L[ℂ] E))
include hκ in

theorem annihilation_extension (L : E →L[ℂ] E) (ξ : E)
    (hDξ : ∀ a : B,star D ((a : E →L[ℂ] E) ξ)=0)
    (hLξ : ∀ a : B,star L ((a : E →L[ℂ] E) ξ)=0)
    (hLD : ∀ a : B,star L*(a : E →L[ℂ] E)*D=0)
    (T : E →L[ℂ] E)
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert (D+star D) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))) :
    star L (T ξ)=0 := by
  let F := (star L) ∘L WithLp.fstL 2 ℂ E E
  have hspan : creationWordSpan B D ξ ξ≤LinearMap.ker F.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    cases w with
    | nil => exact hLξ a
    | cons b w => exact DFunLike.congr_fun (hLD a) (creationWord B D ξ b w)
  have hclosure := (creationWordSpan B D ξ ξ).topologicalClosure_minimal hspan F.isClosed_ker
  exact hclosure (bicommutant_pair_creationWord B D κ hκ ξ ξ hDξ hDξ T hT)
end FreeGroupFactorMain.GaussianExtension

end

end OAI
