import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteSignCharts

namespace OAI

section
namespace ElementaryPositivity.FiniteRayGeometry
noncomputable section
open Module
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma dual_avoid_in_annihilator (r : E) (W : Finset E)
    (hW : ∀w∈W,w∉Submodule.span ℝ {r}) :
    ∃g : Module.Dual ℝ E,g r=0 ∧ ∀w∈W,g w≠0 := by
  let P:=Submodule.span ℝ {r}
  let q:=P.mkQ
  have H : ∀w : W,q w.val≠0:=by
    intro w hw
    exact hW w.val w.property ((Submodule.Quotient.mk_eq_zero P).mp hw)
  obtain ⟨f,hf⟩:=Module.exists_dual_forall_apply_ne_zero (K:=ℝ) (fun w : W=>q w.val) H
  refine ⟨f.comp q,?_,?_⟩
  · have hr : r∈P:=Submodule.subset_span (Set.mem_singleton r)
    simp only [LinearMap.comp_apply,show q r=0 from (Submodule.Quotient.mk_eq_zero P).mpr hr,map_zero]
  · intro w hw
    exact hf ⟨w,hw⟩

lemma scalar_sign_epsilon (a b : ℝ) : ∃ε>0,∀δ:ℝ,0<δ → δ<ε →
    (0<a → 0<a+δ*b) ∧ (a<0 → a+δ*b<0) ∧ (a=0 → b≠0 → a+δ*b≠0) := by
  by_cases ha : a=0
  · refine ⟨1,one_pos,?_⟩
    intro δ hd _
    simp [ha,ne_of_gt hd]
  · have hp : 0 < |b|+1:=by positivity
    refine ⟨|a|/(|b|+1),div_pos (abs_pos.mpr ha) hp,?_⟩
    intro δ hd he
    have H:=(lt_div_iff₀ hp).mp he
    have hlo:=mul_le_mul_of_nonneg_left (neg_abs_le b) hd.le
    have hhi:=mul_le_mul_of_nonneg_left (le_abs_self b) hd.le
    refine ⟨?_,?_,fun h=>False.elim (ha h)⟩
    · intro h; rw [abs_of_pos h] at H; nlinarith
    · intro h; rw [abs_of_neg h] at H; nlinarith

lemma preserve_finite_signs (S : Finset E) (k g : Module.Dual ℝ E) :
    ∃ε>0,∀δ:ℝ,0<δ → δ<ε → ∀s∈S,
      (0<k s → 0<(k+δ • g) s) ∧ (k s<0 → (k+δ • g) s<0) ∧
      (k s=0 → g s≠0 → (k+δ • g) s≠0) := by
  classical
  induction S using Finset.induction_on with
  | empty=>exact ⟨1,one_pos,fun _ _ _ _ hs=>False.elim (Finset.notMem_empty _ hs)⟩
  | @insert s S hs ih=>
    obtain ⟨ε,he,Hε⟩:=ih
    obtain ⟨η,hh,Hη⟩:=scalar_sign_epsilon (k s) (g s)
    refine ⟨min ε η,lt_min he hh,?_⟩
    intro δ hd hδε x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact Hη δ hd (lt_of_lt_of_le hδε (min_le_right _ _))
    · exact Hε δ hd (lt_of_lt_of_le hδε (min_le_left _ _)) x hx

lemma generic_offset (r : E) (W S : Finset E) (k : Module.Dual ℝ E)
    (hk : k r=0) (hW : ∀w∈W,w∉Submodule.span ℝ {r}) :
    ∃h : Module.Dual ℝ E,h r=0 ∧ (∀w∈W,h w≠0) ∧
      ∀s∈S,(0<k s → 0<h s) ∧ (k s<0 → h s<0) := by
  classical
  obtain ⟨g,hgr,hg⟩:=dual_avoid_in_annihilator r W hW
  obtain ⟨ε,he,Hε⟩:=preserve_finite_signs (W∪S) k g
  let δ:=ε/2
  have hd : 0<δ:=by dsimp [δ]; positivity
  have hδε : δ<ε:=by dsimp [δ]; linarith
  refine ⟨k+δ • g,by simp [hk,hgr],?_,?_⟩
  · intro w hw
    have H:=Hε δ hd hδε w (Finset.mem_union_left _ hw)
    rcases lt_trichotomy (k w) 0 with hh|hh|hh
    · exact ne_of_lt (H.2.1 hh)
    · exact H.2.2 hh (hg w hw)
    · exact ne_of_gt (H.1 hh)
  · intro s hs
    have H:=Hε δ hd hδε s (Finset.mem_union_right _ hs)
    exact ⟨H.1,H.2.1⟩

def forbidden (S : Finset E) (r : E) (v : Module.Dual ℝ E) : Finset E := by
  classical
  exact (S ∪ (S×ˢS).image (fun st=>v st.1 • st.2-v st.2 • st.1)).filter
    (fun w=>w∉Submodule.span ℝ {r})

structure GenericOffset (S : Finset E) (r : E) (v h : Module.Dual ℝ E) : Prop where
  on_ray : h r=0
  avoid : ∀s∈S,s∉Submodule.span ℝ {r} → h s≠0
  distinct : ∀s∈S,∀t∈S,v s • t-v t • s∉Submodule.span ℝ {r} →
    h (v s • t-v t • s)≠0

lemma exists_generic_offset (S : Finset E) (r : E) (v k : Module.Dual ℝ E)
    (hk : k r=0) : ∃h : Module.Dual ℝ E,GenericOffset S r v h ∧
      ∀s∈S,(0<k s → 0<h s) ∧ (k s<0 → h s<0) := by
  classical
  obtain ⟨h,hr,hW,hS⟩:=generic_offset r (forbidden S r v) S k hk
    (fun w hw=>(Finset.mem_filter.mp hw).2)
  refine ⟨h,⟨hr,?_,?_⟩,hS⟩
  · intro s hs hn
    exact hW s (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hs,hn⟩)
  · intro s hs t ht hn
    exact hW _ (Finset.mem_filter.mpr ⟨Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,rfl⟩),hn⟩)

lemma GenericOffset.parallel_avoided {S : Finset E} {r : E} {v h : Module.Dual ℝ E}
    (H : GenericOffset S r v h) {s : E} (hs : s∈S) (hn : s∉Submodule.span ℝ {r})
    (hv : v s=0) (a : ℝ) : (h+a • v) s≠0 := by
  simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hv,mul_zero,add_zero]
    using H.avoid s hs hn

lemma GenericOffset.joint_plane {S : Finset E} {r : E} {v h : Module.Dual ℝ E}
    (H : GenericOffset S r v h) {s t : E} (hs : s∈S) (ht : t∈S) (hv : v s≠0)
    (a : ℝ) (hsa : (h+a • v) s=0) (hta : (h+a • v) t=0) :
    t∈Submodule.span ℝ {r,s} := by
  classical
  have hw : v s • t-v t • s∈Submodule.span ℝ {r}:=by
    by_contra hn
    apply H.distinct s hs t ht hn
    simp only [map_sub,map_smul,smul_eq_mul]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at hsa hta
    have hs0 : h s = -a * v s := by linarith
    have ht0 : h t = -a * v t := by linarith
    rw [hs0,ht0]
    ring
  have hw' : v s • t-v t • s∈Submodule.span ℝ {r,s}:=
    (Submodule.span_mono (by simp : ({r}:Set E)⊆{r,s})) hw
  have hs' : s∈Submodule.span ℝ {r,s}:=Submodule.subset_span (by simp)
  have Hst:= (Submodule.span ℝ {r,s}).add_mem hw'
    ((Submodule.span ℝ {r,s}).smul_mem (v t) hs')
  simp only [sub_add_cancel] at Hst
  exact ((Submodule.span ℝ {r,s}).smul_mem_iff hv).mp Hst

end
end ElementaryPositivity.FiniteRayGeometry

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (e : M →+ E) (he : Function.Injective e) (C : (I → ℤ) →+ M)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hdeg in
lemma positive_ray_of_mem_span (r p : M) (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (hr : HasRootDegree C d r) (hp : HasRootDegree C n p)
    (H : e p∈Submodule.span ℝ {e r}) : OnPositiveRay r p := by
  obtain ⟨a,ha⟩:=Submodule.mem_span_singleton.mp H
  have HLa:=congrArg L ha
  simp only [map_smul,smul_eq_mul,hdeg d r hr,hdeg n p hp] at HLa
  refine ⟨d,n,hd,hn,he ?_⟩
  simp only [map_nsmul,←Nat.cast_smul_eq_nsmul ℝ]
  rw [←ha,smul_smul]
  congr 1
  nlinarith only [HLa]

def lineEvents (S : Finset E) (v h : Module.Dual ℝ E) : Finset ℝ := by
  classical
  exact (S.filter (fun s => v s≠0)).image (fun s => -h s/v s)
lemma mem_lineEvents_iff (S : Finset E) (v h : Module.Dual ℝ E) (a : ℝ) :
    a∈lineEvents S v h ↔ ∃s∈S,v s≠0 ∧ (h+a • v) s=0 := by
  classical
  constructor
  · rintro ha
    obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨hs,hn⟩:=Finset.mem_filter.mp hs
    refine ⟨s,hs,hn,?_⟩
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
    field_simp
    ring
  · rintro ⟨s,hs,hn,H⟩
    apply Finset.mem_image.mpr
    refine ⟨s,Finset.mem_filter.mpr ⟨hs,hn⟩,?_⟩
    apply (div_eq_iff hn).mpr
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at H
    linarith

def realRootsThrough (N : ℕ) : Finset E := by
  classical
  exact (rootsThrough C N).image e
omit [Module ℝ E] in
lemma realRoot_mem (N n : ℕ) (hn : n ≤ N) (m : M) (hm : HasRootDegree C n m) :
    e m∈realRootsThrough e C N := by
  classical
  exact Finset.mem_image.mpr ⟨m,mem_rootsThrough C N n hn m hm,rfl⟩
include he hdeg in
lemma line_generic (N d : ℕ) (r : M) (hd : 0 < d) (hr : HasRootDegree C d r)
    (v h : Module.Dual ℝ E) (hv : v (e r)=0)
    (H : GenericOffset (realRootsThrough e C N) (e r) v h)
    (a : ℝ) (ha : a∉lineEvents (realRootsThrough e C N) v h) :
    RayGeneric C N r ((h+a • v).toAddMonoidHom.comp e) := by
  constructor
  · change h (e r)+a*v (e r)=0
    rw [H.on_ray,hv,mul_zero,add_zero]
  · intro n hn hnN m hm hm0
    have hmS:=realRoot_mem e C N n hnN m hm
    by_cases hmP : e m∈Submodule.span ℝ {e r}
    · exact positive_ray_of_mem_span e he C L hdeg r m d n hd hn hr hm hmP
    · by_cases hvm : v (e m)=0
      · exact False.elim ((H.parallel_avoided hmS hmP hvm a) hm0)
      · exact False.elim (ha ((mem_lineEvents_iff _ _ _ _).mpr ⟨e m,hmS,hvm,hm0⟩))

lemma real_line_signs (u w a b : ℝ) (hw : w≠0) (ha : a≠ -u/w) (hb : b≠ -u/w)
    (H : a < -u/w ↔ b < -u/w) :
    (0 < u+a*w → 0 < u+b*w) ∧ (u+a*w=0 → u+b*w=0) ∧ (u+a*w < 0 → u+b*w < 0) := by
  have hz : u+(-u/w)*w=0:=by field_simp; ring
  by_cases has : a < -u/w
  · have hbs:=H.mp has
    rcases lt_or_gt_of_ne hw with hw|hw
    · have ha' : 0 < u+a*w:=by nlinarith
      have hb' : 0 < u+b*w:=by nlinarith
      exact ⟨fun _ => hb',fun h => by linarith,fun h => by linarith⟩
    · have ha' : u+a*w < 0:=by nlinarith
      have hb' : u+b*w < 0:=by nlinarith
      exact ⟨fun h => by linarith,fun h => by linarith,fun _ => hb'⟩
  · have hza : -u/w < a:=lt_of_le_of_ne (le_of_not_gt has) (Ne.symm ha)
    have hzb : -u/w < b:=lt_of_le_of_ne (le_of_not_gt (fun hh => has (H.mpr hh))) (Ne.symm hb)
    rcases lt_or_gt_of_ne hw with hw|hw
    · have ha' : u+a*w < 0:=by nlinarith
      have hb' : u+b*w < 0:=by nlinarith
      exact ⟨fun h => by linarith,fun h => by linarith,fun _ => hb'⟩
    · have ha' : 0 < u+a*w:=by nlinarith
      have hb' : 0 < u+b*w:=by nlinarith
      exact ⟨fun _ => hb',fun h => by linarith,fun h => by linarith⟩
lemma line_cell_signs (S : Finset E) (v h : Module.Dual ℝ E) (a b : ℝ)
    (ha : a∉lineEvents S v h) (hb : b∉lineEvents S v h)
    (H : ∀z∈lineEvents S v h,a < z ↔ b < z) (s : E) (hs : s∈S) :
    (0 < (h+a • v) s → 0 < (h+b • v) s) ∧
    ((h+a • v) s=0 → (h+b • v) s=0) ∧ ((h+a • v) s < 0 → (h+b • v) s < 0) := by
  classical
  by_cases hw : v s=0
  · simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hw,mul_zero,add_zero]
    exact ⟨id,id,id⟩
  · have hz : -h s/v s∈lineEvents S v h:=Finset.mem_image.mpr
      ⟨s,Finset.mem_filter.mpr ⟨hs,hw⟩,rfl⟩
    exact real_line_signs (h s) (v s) a b hw (fun he => ha (he ▸ hz))
      (fun he => hb (he ▸ hz)) (H _ hz)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
