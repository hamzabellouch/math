import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.Vertex
import OAI.Probability.LogConcave.JetEstimates.MultisetProd

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

def inside (b : P → Point d) (f : P → Point d → ℝ) (S : State P) (j : P) : Point d → ℝ :=
  JetCalculus.jet b (S.derivatives j) (f j)

def primary (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (j : P) : Point d → ℝ :=
  if j∈S.pending then adjointCoordinate H (b j) (inside b f S j) else inside b f S j

def hessian (H : Point d → ℝ) (b : P → Point d) (h : Hessian P) : Point d → ℝ :=
  JetCalculus.jet b h.extra (directional (b h.first) (directional (b h.second) H))

def term (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (x : Point d) : ℝ :=
  (∏j,primary H b f S j x)*(S.hessians.map (fun h => hessian H b h x)).prod

omit [Fintype P] [DecidableEq P] in
lemma hessian_hit (H : Point d → ℝ) (b : P → Point d) (h : Hessian P) (i : P) :
    hessian H b (h.hit i)=directional (b i) (hessian H b h) := rfl

lemma term_split (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (i : P) (x : Point d) :
    term H b f S x=primary H b f S i x*(∏j∈Finset.univ.erase i,primary H b f S j x)*
      (S.hessians.map (fun h => hessian H b h x)).prod := by
  unfold term
  congr 1
  exact (Finset.mul_prod_erase Finset.univ (fun j => primary H b f S j x) (Finset.mem_univ i)).symm

omit [Fintype P] in
lemma primary_congr (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S T : State P) (j : P) (hp : j∈S.pending ↔ j∈T.pending)
    (hd : S.derivatives j=T.derivatives j) : primary H b f S j=primary H b f T j := by
  unfold primary
  by_cases hs : j∈S.pending
  · rw [ite_eq_left hs,ite_eq_left (hp.mp hs)]
    congr 1
    unfold inside
    rw [hd]
  · rw [ite_eq_right hs,ite_eq_right (fun ht => hs (hp.mpr ht))]
    unfold inside
    rw [hd]

lemma hitPrimary_term (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) {i j : P} (hij : i≠j) (x : Point d) :
    term H b f (hitPrimary S i j) x=
      inside b f S i x*
      (if j∈S.pending then adjointCoordinate H (b j) (directional (b i) (inside b f S j)) x
        else directional (b i) (inside b f S j) x)*
      (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
      (S.hessians.map (fun h => hessian H b h x)).prod := by
  have hj : j∈Finset.univ.erase i := by simp [hij.symm]
  rw [term_split H b f _ i x,←Finset.mul_prod_erase (Finset.univ.erase i)
    (fun k => primary H b f (hitPrimary S i j) k x) hj]
  have hi' : primary H b f (hitPrimary S i j) i=inside b f S i := by
    simp [primary,inside,hitPrimary,Function.update_of_ne hij]
  have hj' : primary H b f (hitPrimary S i j) j=
      fun x => if j∈S.pending then adjointCoordinate H (b j) (directional (b i) (inside b f S j)) x
        else directional (b i) (inside b f S j) x := by
    simp only [primary,inside,hitPrimary,Function.update_self,JetCalculus.jet,
      Finset.mem_erase,hij.symm,ne_eq,not_false_eq_true,true_and]
    split_ifs <;> rfl
  have hr : (∏k∈(Finset.univ.erase i).erase j,primary H b f (hitPrimary S i j) k x)=
      ∏k∈(Finset.univ.erase i).erase j,primary H b f S k x := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj := (Finset.mem_erase.mp hk).1
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    apply congrFun (primary_congr H b f (hitPrimary S i j) S k ?_ ?_) x
    · exact ⟨fun ht => (Finset.mem_erase.mp ht).2,fun ht => Finset.mem_erase.mpr ⟨hki,ht⟩⟩
    · exact Function.update_of_ne hkj _ _
  rw [hi',hj',hr]
  dsimp only [hitPrimary]
  ring

lemma pair_term (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) {i j : P} (hij : i≠j) (x : Point d) :
    term H b f (pair S i j) x=
      inside b f S i x*directional (b i) (directional (b j) H) x*inside b f S j x*
      (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
      (S.hessians.map (fun h => hessian H b h x)).prod := by
  have hj : j∈Finset.univ.erase i := by simp [hij.symm]
  rw [term_split H b f _ i x,←Finset.mul_prod_erase (Finset.univ.erase i)
    (fun k => primary H b f (pair S i j) k x) hj]
  have hi' : primary H b f (pair S i j) i=inside b f S i := by simp [primary,inside,pair]
  have hj' : primary H b f (pair S i j) j=inside b f S j := by simp [primary,inside,pair]
  have hr : (∏k∈(Finset.univ.erase i).erase j,primary H b f (pair S i j) k x)=
      ∏k∈(Finset.univ.erase i).erase j,primary H b f S k x := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj := (Finset.mem_erase.mp hk).1
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    apply congrFun (primary_congr H b f (pair S i j) S k ?_ rfl) x
    exact ⟨fun ht => (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).2,
      fun ht => Finset.mem_erase.mpr ⟨hkj,Finset.mem_erase.mpr ⟨hki,ht⟩⟩⟩
  rw [hi',hj',hr]
  simp only [pair,Multiset.map_cons,Multiset.prod_cons,hessian,JetCalculus.jet]
  ring

lemma hitHessian_term (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (i : P) (h : Hessian P) (x : Point d) :
    term H b f (hitHessian S i h) x=
      inside b f S i x*(∏j∈Finset.univ.erase i,primary H b f S j x)*
      directional (b i) (hessian H b h) x*
      ((S.hessians.erase h).map (fun g => hessian H b g x)).prod := by
  rw [term_split H b f _ i x]
  have hi' : primary H b f (hitHessian S i h) i=inside b f S i := by
    simp [primary,inside,hitHessian]
  have hr : (∏j∈Finset.univ.erase i,primary H b f (hitHessian S i h) j x)=
      ∏j∈Finset.univ.erase i,primary H b f S j x := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    apply congrFun (primary_congr H b f (hitHessian S i h) S j ?_ rfl) x
    exact ⟨fun ht => (Finset.mem_erase.mp ht).2,fun ht => Finset.mem_erase.mpr ⟨hji,ht⟩⟩
  rw [hi',hr]
  simp only [hitHessian,Multiset.map_cons,Multiset.prod_cons,hessian_hit]
  ring

structure Regular (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (K : ℝ≥0) : Prop where
  smooth_H : ContDiff ℝ (⊤ : ℕ∞) H
  tail : HasGaussianLowerTail H
  lipschitz : LipschitzWith K (gradient H)
  smooth_f : ∀j,ContDiff ℝ (⊤ : ℕ∞) (f j)
  primary_jets : ∀j l,PolyC1 (JetCalculus.jet b l (f j))
  hessian_jets : ∀h : Hessian P,PolyC1 (hessian H b h)

omit [Fintype P] in
lemma Regular.primary_polyC1 {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) (j : P) : PolyC1 (primary H b f S j) := by
  unfold primary
  split_ifs
  · exact polyC1_adjointCoordinate h.smooth_H h.lipschitz (h.primary_jets j _) (b j)
      (h.primary_jets j (j::S.derivatives j))
  · exact h.primary_jets j _

lemma Regular.term_polyC1 {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) : PolyC1 (term H b f S) :=
  (PolyC1.prod Finset.univ (fun j _ => h.primary_polyC1 S j)).mul
    (PolyC1.multisetProd _ (fun h' _ => h.hessian_jets h'))

lemma Regular.integrable_term {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) : Integrable (term H b f S) (gibbs H) :=
  integrable_polynomial_gibbs h.smooth_H.continuous h.tail (h.term_polyC1 S).continuous (h.term_polyC1 S).growth

omit [Fintype P] in
lemma primary_directional {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) (i j : P) :
    directional (b i) (primary H b f S j)=fun x =>
      (if j∈S.pending then adjointCoordinate H (b j) (directional (b i) (inside b f S j)) x
        else directional (b i) (inside b f S j) x)+
      (if j∈S.pending then directional (b i) (directional (b j) H) x*inside b f S j x else 0) := by
  unfold primary
  split_ifs with hj
  · exact directional_adjointCoordinate h.smooth_H (JetCalculus.smooth_jet (h.smooth_f j) b _) _ _
  · funext x; simp
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

lemma primary_branch_integrand {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) {i j : P} (hij : i≠j) (x : Point d) :
    inside b f S i x*directional (b i) (primary H b f S j) x*
      (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
      (S.hessians.map (fun g => hessian H b g x)).prod=
      term H b f (hitPrimary S i j) x+(if j∈S.pending then term H b f (pair S i j) x else 0) := by
  rw [primary_directional h,hitPrimary_term _ _ _ _ hij]
  by_cases hj : j∈S.pending
  · simp only [hj,ite_true,pair_term _ _ _ _ hij]
    ring
  · simp only [hj,ite_false,add_zero]

lemma pending_sum {S : State P} (i : P) (F : P → ℝ) :
    (∑j∈Finset.univ.erase i,if j∈S.pending then F j else 0)=∑j∈S.pending.erase i,F j := by
  rw [←Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true]

theorem integral_one_step {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (S : State P) {i : P} (hi : i∈S.pending) :
    (∫x,term H b f S x ∂gibbs H)=
      ((branches S i).map (fun T => ∫x,term H b f T x ∂gibbs H)).sum := by
  have he := adjointCoordinate_mixed_product_pairing
    (h.smooth_H.of_le (by simp)) h.tail h.lipschitz (h.primary_jets i (S.derivatives i))
    (Finset.univ.erase i) (fun j _ => h.primary_polyC1 S j)
    S.hessians (fun g _ => h.hessian_jets g) (b i)
  have hleft : (fun x => adjointCoordinate H (b i) (inside b f S i) x*
      (∏j∈Finset.univ.erase i,primary H b f S j x)*
      (S.hessians.map (fun g => hessian H b g x)).prod)=term H b f S := by
    funext x
    rw [term_split H b f S i x]
    simp only [primary,hi,ite_true]
  change (∫x,adjointCoordinate H (b i) (inside b f S i) x*
      (∏j∈Finset.univ.erase i,primary H b f S j x)*
      (S.hessians.map (fun g => hessian H b g x)).prod ∂gibbs H)=_ at he
  rw [hleft] at he
  rw [he]
  have hp (j : P) (hj : j∈Finset.univ.erase i) :
      (∫x,inside b f S i x*directional (b i) (primary H b f S j) x*
        (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
        (S.hessians.map (fun g => hessian H b g x)).prod ∂gibbs H)=
      (∫x,term H b f (hitPrimary S i j) x ∂gibbs H)+
        (if j∈S.pending then ∫x,term H b f (pair S i j) x ∂gibbs H else 0) := by
    have hij := (Finset.mem_erase.mp hj).1.symm
    simp_rw [primary_branch_integrand h S hij]
    by_cases hj' : j∈S.pending
    · simp only [hj',ite_true]
      exact integral_add (h.integrable_term _) (h.integrable_term _)
    · simp only [hj',ite_false,add_zero]
  have hs : (∑j∈Finset.univ.erase i,∫x,inside b f S i x*directional (b i) (primary H b f S j) x*
        (∏k∈(Finset.univ.erase i).erase j,primary H b f S k x)*
        (S.hessians.map (fun g => hessian H b g x)).prod ∂gibbs H)=
      (∑j∈Finset.univ.erase i,∫x,term H b f (hitPrimary S i j) x ∂gibbs H)+
      (∑j∈S.pending.erase i,∫x,term H b f (pair S i j) x ∂gibbs H) := by
    rw [Finset.sum_congr rfl hp,Finset.sum_add_distrib,pending_sum]
  simp only [inside] at hs
  rw [hs]
  have hh : (S.hessians.map (fun g => ∫x,inside b f S i x*
      (∏j∈Finset.univ.erase i,primary H b f S j x)*directional (b i) (hessian H b g) x*
      ((S.hessians.erase g).map (fun g' => hessian H b g' x)).prod ∂gibbs H)).sum=
      (S.hessians.map (fun g => ∫x,term H b f (hitHessian S i g) x ∂gibbs H)).sum := by
    simp_rw [hitHessian_term]
  simp only [inside] at hh
  rw [hh]
  simp only [branches,List.map_append,List.map_map,List.sum_append,Function.comp_def]
  have hfins (s : Finset P) (F : P → ℝ) : (s.toList.map F).sum=∑j∈s,F j := by
    simp
  rw [hfins,hfins]
  congr 1
  have hh := congrArg (fun ms : Multiset (Hessian P) =>
    (ms.map (fun g => ∫x,term H b f (hitHessian S i g) x ∂gibbs H)).sum) S.hessians.coe_toList
  simp

omit [Fintype P] [DecidableEq P] in
lemma list_sum_map_flatMap {α β : Type*} (L : List α) (B : α → List β) (F : β → ℝ) :
    ((L.flatMap B).map F).sum=(L.map (fun a => ((B a).map F).sum)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,ih]

theorem integral_expand {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) (n : ℕ) (S : State P) :
    (∫x,term H b f S x ∂gibbs H)=
      ((expand n S).map (fun T => ∫x,term H b f T x ∂gibbs H)).sum := by
  induction n generalizing S with
  | zero => simp [expand]
  | succ n ih =>
    simp only [expand]
    split_ifs with hp
    · rw [list_sum_map_flatMap,integral_one_step h S (Classical.choose_spec hp)]
      apply congrArg List.sum
      apply List.map_congr_left
      intro T _
      exact ih T
    · simp

lemma term_terminal (H : Point d → ℝ) (b : P → Point d) (f : P → Point d → ℝ)
    (S : State P) (hS : S.pending=∅) :
    term H b f S=fun x => (∏j,JetCalculus.jet b (S.derivatives j) (f j) x)*
      (S.hessians.map (fun h => hessian H b h x)).prod := by
  funext x
  simp [term,primary,inside,hS]

theorem actual_adjoint_expansion {H : Point d → ℝ} {b : P → Point d} {f : P → Point d → ℝ}
    {K : ℝ≥0} (h : Regular H b f K) :
    (∫x,(∏j,adjointCoordinate H (b j) (f j) x) ∂gibbs H)=
      ((expand (Fintype.card P) initial).map (fun S =>
        ∫x,(∏j,JetCalculus.jet b (S.derivatives j) (f j) x)*
          (S.hessians.map (fun h => hessian H b h x)).prod ∂gibbs H)).sum := by
  have he := integral_expand h (Fintype.card P) initial
  have hi : term H b f initial=fun x => ∏j,adjointCoordinate H (b j) (f j) x := by
    funext x
    simp [term,primary,inside,initial,JetCalculus.jet]
  rw [hi] at he
  rw [he]
  apply congrArg List.sum
  apply List.map_congr_left
  intro S hS
  rw [term_terminal H b f S (mem_expand_terminal (by simp [initial]) hS)]
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped RealInnerProductSpace NNReal

variable {d : ℕ} {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P]

lemma product_tensorAdjoint (H : Point d → ℝ) (b : I → Point d)
    (f : P → I → Point d → ℝ) (x : Point d) :
    (∏p,tensorAdjoint H b (f p) x)=
      ∑a : P → I,∏p,adjointCoordinate H (b (a p)) (f p (a p)) x := by
  classical
  simp only [tensorAdjoint]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]

theorem tensor_actual_adjoint_expansion
    {H : Point d → ℝ} {b : I → Point d} {f : P → I → Point d → ℝ}
    {K : ℝ≥0}
    (h : ∀a : P → I,Regular H (fun p => b (a p)) (fun p => f p (a p)) K) :
    (∫x,(∏p,tensorAdjoint H b (f p) x) ∂gibbs H)=
      ∑a : P → I,((expand (Fintype.card P) initial).map (fun S =>
        ∫x,(∏p,JetCalculus.jet (fun q => b (a q)) (S.derivatives p) (f p (a p)) x)*
          (S.hessians.map (fun h => hessian H (fun q => b (a q)) h x)).prod ∂gibbs H)).sum := by
  classical
  simp_rw [product_tensorAdjoint]
  have hi (a : P → I) : Integrable
      (fun x => ∏p,adjointCoordinate H (b (a p)) (f p (a p)) x) (gibbs H) := by
    have hh := (h a).integrable_term initial
    have he : term H (fun p => b (a p)) (fun p => f p (a p)) initial=
        fun x => ∏p,adjointCoordinate H (b (a p)) (f p (a p)) x := by
      funext x
      simp [term,primary,inside,initial,JetCalculus.jet]
    rwa [he] at hh
  rw [integral_finsetSum Finset.univ (fun a _ => hi a)]
  exact Finset.sum_congr rfl (fun a _ => actual_adjoint_expansion (h a))

theorem tensor_actual_adjoint_expansion_branch_first
    {H : Point d → ℝ} {b : I → Point d} {f : P → I → Point d → ℝ}
    {K : ℝ≥0}
    (h : ∀a : P → I,Regular H (fun p => b (a p)) (fun p => f p (a p)) K) :
    (∫x,(∏p,tensorAdjoint H b (f p) x) ∂gibbs H)=
      ((expand (Fintype.card P) initial).map (fun S =>
        ∑a : P → I,∫x,(∏p,JetCalculus.jet (fun q => b (a q)) (S.derivatives p) (f p (a p)) x)*
          (S.hessians.map (fun h => hessian H (fun q => b (a q)) h x)).prod ∂gibbs H)).sum := by
  classical
  rw [tensor_actual_adjoint_expansion h]
  generalize expand (Fintype.card P) (initial (P:=P)) = L
  induction L with
  | nil => simp
  | cons S L ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
