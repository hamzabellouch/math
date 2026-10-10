import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteRayGeometry

namespace OAI

section
namespace ElementaryPositivity.FiniteRayGeometry
open Module
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma preserve_finite_affine_signs (P : Finset (ℝ×E)) (k g v : Module.Dual ℝ E) :
    ∃ε>0,∀δ:ℝ,0<δ → δ<ε → ∀as∈P,
      (0<(k+as.1 • v) as.2 → 0<(k+δ • g+as.1 • v) as.2) ∧
      ((k+as.1 • v) as.2<0 → (k+δ • g+as.1 • v) as.2<0) := by
  classical
  induction P using Finset.induction_on with
  | empty=>exact ⟨1,one_pos,fun _ _ _ _ hs=>False.elim (Finset.notMem_empty _ hs)⟩
  | @insert a P ha ih=>
    obtain ⟨ε,hε,Hε⟩:=ih
    obtain ⟨η,hη,Hη⟩:=scalar_sign_epsilon ((k+a.1 • v) a.2) (g a.2)
    refine ⟨min ε η,lt_min hε hη,?_⟩
    intro δ hd he as has
    rcases Finset.mem_insert.mp has with rfl|has
    · have H:=Hη δ hd (lt_of_lt_of_le he (min_le_right _ _))
      simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,add_right_comm]
        using And.intro H.1 H.2.1
    · exact Hε δ hd (lt_of_lt_of_le he (min_le_left _ _)) as has

lemma exists_generic_offset_with_probes (T : Finset E) (r : E)
    (P : Finset (ℝ×E)) (v k : Module.Dual ℝ E) (hk : k r=0) :
    ∃h : Module.Dual ℝ E,GenericOffset T r v h ∧ ∀as∈P,
      (0<(k+as.1 • v) as.2 → 0<(h+as.1 • v) as.2) ∧
      ((k+as.1 • v) as.2<0 → (h+as.1 • v) as.2<0) := by
  classical
  let W:=forbidden T r v
  obtain ⟨g,hgr,hg⟩:=dual_avoid_in_annihilator r W
    (fun w hw=>(Finset.mem_filter.mp hw).2)
  obtain ⟨ε,hε,Hε⟩:=preserve_finite_signs W k g
  obtain ⟨η,hη,Hη⟩:=preserve_finite_affine_signs P k g v
  let δ:=min ε η/2
  have hd : 0<δ:=by dsimp [δ]; positivity
  have hdε : δ<ε:=by dsimp [δ]; have :=min_le_left ε η; have :=lt_min hε hη; linarith
  have hdη : δ<η:=by dsimp [δ]; have :=min_le_right ε η; have :=lt_min hε hη; linarith
  have Havoid : ∀w∈W,(k+δ • g) w≠0:=by
    intro w hw
    have H:=Hε δ hd hdε w hw
    rcases lt_trichotomy (k w) 0 with hz|hz|hz
    · exact ne_of_lt (H.2.1 hz)
    · exact H.2.2 hz (hg w hw)
    · exact ne_of_gt (H.1 hz)
  refine ⟨k+δ • g,⟨by simp [hk,hgr],?_,?_⟩,Hη δ hd hdη⟩
  · intro s hs hn
    exact Havoid s (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs,hn⟩)
  · intro s hs t ht hn
    exact Havoid _ (Finset.mem_filter.mpr ⟨Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩)
lemma affine_event_between (u w a b : ℝ) (ha : u+a*w<0) (hb : 0<u+b*w)
    (hab : a<b) : a< -u/w ∧ -u/w<b := by
  have hw : 0<w:=by nlinarith
  constructor
  · apply (lt_div_iff₀ hw).mpr; linarith
  · apply (div_lt_iff₀ hw).mpr; linarith

lemma perturbed_event_between (k h v : Module.Dual ℝ E) (a b : ℝ) (s : E)
    (hab : a<b) (ha : (k+a • v) s<0) (hb : 0<(k+b • v) s)
    (hpa : (k+a • v) s<0 → (h+a • v) s<0)
    (hpb : 0<(k+b • v) s → 0<(h+b • v) s) :
    a< -h s/v s ∧ -h s/v s<b := by
  exact affine_event_between (h s) (v s) a b (hpa ha) (hpb hb) hab
end
end ElementaryPositivity.FiniteRayGeometry

end
section
namespace ElementaryPositivity.FiniteRayGeometry
open Module Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma dense_annihilator_avoid (r w : E) (hw : w∉Submodule.span ℝ {r}) :
    Dense {h : (ContinuousLinearMap.apply ℝ ℝ r).ker | h.val w≠0} := by
  classical
  let A:=(ContinuousLinearMap.apply ℝ ℝ r).ker
  let f : A →ₗ[ℝ] ℝ := (ContinuousLinearMap.apply ℝ ℝ w).toLinearMap.comp A.subtype
  have hf : f≠0:=by
    obtain ⟨g,hgr,hgw⟩:=dual_avoid_in_annihilator r {w} (by simpa using hw)
    let gc : E →L[ℝ] ℝ:=LinearMap.toContinuousLinearMap g
    let a : A:=⟨gc,by change g r=0; exact hgr⟩
    intro hz
    have H:=LinearMap.congr_fun hz a
    change g w=0 at H
    exact hgw w (Finset.mem_singleton_self w) H
  have hi : interior (f.ker:Set A)=∅:=by
    by_contra hh
    exact hf (LinearMap.ker_eq_top.mp (Submodule.eq_top_of_nonempty_interior' f.ker
      (Set.nonempty_iff_ne_empty.mpr hh)))
  exact interior_eq_empty_iff_dense_compl.mp hi

lemma countable_avoid_with_probes (W : Set E) (hW : W.Countable) (r : E)
    (hproper : ∀w∈W,w∉Submodule.span ℝ {r})
    (P : Finset (ℝ×E)) (v k : Module.Dual ℝ E) (hk : k r=0) :
    ∃h : Module.Dual ℝ E,h r=0 ∧ (∀w∈W,h w≠0) ∧ ∀as∈P,
      (0<(k+as.1 • v) as.2 → 0<(h+as.1 • v) as.2) ∧
      ((k+as.1 • v) as.2<0 → (h+as.1 • v) as.2<0) := by
  classical
  let A:=(ContinuousLinearMap.apply ℝ ℝ r).ker
  let U : Set A:={h|∀as∈P,
    (0<(k+as.1 • v) as.2 → 0<h.val as.2+as.1*v as.2) ∧
    ((k+as.1 • v) as.2<0 → h.val as.2+as.1*v as.2<0)}
  have hU : IsOpen U:=by
    have H : ∀as : ℝ×E,IsOpen {h:A|
        (0<(k+as.1 • v) as.2 → 0<h.val as.2+as.1*v as.2) ∧
        ((k+as.1 • v) as.2<0 → h.val as.2+as.1*v as.2<0)}:=by
      intro as
      have hc : Continuous (fun h:A=>h.val as.2+as.1*v as.2):=
        ((ContinuousLinearMap.apply ℝ ℝ as.2).continuous.comp continuous_subtype_val).add continuous_const
      by_cases hp : 0<(k+as.1 • v) as.2 <;>
      by_cases hn : (k+as.1 • v) as.2<0 <;>
        simp only [hp,hn,IsEmpty.forall_iff,forall_const,true_and,and_true]
      · exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
      · exact isOpen_lt continuous_const hc
      · exact isOpen_lt hc continuous_const
      · exact isOpen_univ
    convert isOpen_biInter_finset (s:=P) (fun as _=>H as) using 1
    ext h; simp only [U,Set.mem_ofPred_eq,Set.mem_iInter]
  have hnU : U.Nonempty:=by
    let kc : E →L[ℝ] ℝ:=LinearMap.toContinuousLinearMap k
    refine ⟨⟨kc,by change k r=0; exact hk⟩,?_⟩
    intro as _
    exact ⟨fun H=>H,fun H=>H⟩
  have Hd : Dense (⋂w∈W,{h:A|h.val w≠0}):=dense_biInter_of_isOpen
    (fun w _=>isOpen_ne_fun ((ContinuousLinearMap.apply ℝ ℝ w).continuous.comp continuous_subtype_val)
      continuous_const) hW (fun w hw=>dense_annihilator_avoid r w (hproper w hw))
  obtain ⟨h,hhU,hh⟩:=Hd.inter_open_nonempty U hU hnU
  refine ⟨h.val.toLinearMap,by exact h.property,?_,?_⟩
  · change ∀w∈W,h.val w≠0
    simpa only [Set.mem_iInter,Set.mem_ofPred_eq] using hh
  · exact hhU

lemma exists_all_generic_offsets_with_probes (T : ℕ → Finset E) (r : E)
    (P : Finset (ℝ×E)) (v k : Module.Dual ℝ E) (hk : k r=0) :
    ∃h : Module.Dual ℝ E,(∀N,GenericOffset (T N) r v h) ∧ ∀as∈P,
      (0<(k+as.1 • v) as.2 → 0<(h+as.1 • v) as.2) ∧
      ((k+as.1 • v) as.2<0 → (h+as.1 • v) as.2<0) := by
  classical
  let W : Set E:=⋃N,↑(forbidden (T N) r v)
  have hW : W.Countable:=Set.countable_iUnion (fun N=>(forbidden (T N) r v).countable_toSet)
  have hp : ∀w∈W,w∉Submodule.span ℝ {r}:=by
    intro w hw
    obtain ⟨N,hN⟩:=Set.mem_iUnion.mp hw
    exact (Finset.mem_filter.mp hN).2
  obtain ⟨h,hr,havoid,H⟩:=countable_avoid_with_probes W hW r hp P v k hk
  refine ⟨h,fun N=>⟨hr,?_,?_⟩,H⟩
  · intro s hs hn
    exact havoid s (Set.mem_iUnion.mpr ⟨N,Finset.mem_filter.mpr
      ⟨Finset.mem_union_left _ hs,hn⟩⟩)
  · intro s hs t ht hn
    exact havoid _ (Set.mem_iUnion.mpr ⟨N,Finset.mem_filter.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩⟩)

end
end ElementaryPositivity.FiniteRayGeometry

end

end OAI
