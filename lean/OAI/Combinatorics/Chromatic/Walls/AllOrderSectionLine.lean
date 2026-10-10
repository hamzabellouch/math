import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FinitePathPerturbation
import OAI.Combinatorics.Chromatic.Walls.SectionRayTransition

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

include he hdeg in
lemma section_event_ray_all_orders (N : ℕ) (v k : Module.Dual ℝ E)
    (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : a∈lineEvents (realRootsThrough e C N) v k) :
    ∃p d,0<d ∧ d≤N ∧ HasRootDegree C d p ∧ v (e p)≠0 ∧
      ∀K,RayGeneric C K p ((k+a • v).toAddMonoidHom.comp e) := by
  obtain ⟨p,d,hd0,hd,hp,hv,hgen⟩:=section_event_ray C e he L hdeg N v k (H N) a ha
  refine ⟨p,d,hd0,hd,hp,hv,fun K=>⟨hgen.1,?_⟩⟩
  intro n hn hnK m hm hm0
  have hpS:=realRoot_mem e C (max N K) d (hd.trans (le_max_left _ _)) p hp
  have hmS:=realRoot_mem e C (max N K) n (hnK.trans (le_max_right _ _)) m hm
  have HH:=(H (max N K)).joint_plane hpS hmS hv a hgen.1 hm0
  apply positive_ray_of_mem_span e he C L hdeg p m d n hd0 hn hp hm
  obtain ⟨x,y,hxy⟩:=Submodule.mem_span_pair.mp HH
  exact Submodule.mem_span_singleton.mpr ⟨y,by simpa only [smul_zero,zero_add] using hxy⟩
end
section Existence
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)

lemma section_all_order_offset (P : Finset (ℝ×E)) (v k : Module.Dual ℝ E) :
    ∃h : Module.Dual ℝ E,(∀N,GenericOffset (realRootsThrough e C N) 0 v h) ∧ ∀as∈P,
      (0<(k+as.1 • v) as.2 → 0<(h+as.1 • v) as.2) ∧
      ((k+as.1 • v) as.2<0 → (h+as.1 • v) as.2<0) :=
  exists_all_generic_offsets_with_probes (realRootsThrough e C) 0 P v k (map_zero k)
end
end Existence
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (C : (I → ℤ) →+ M) (e : M →+ E)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

include hdeg in
lemma line_chamber_of_not_event (N : ℕ) (v k : Module.Dual ℝ E)
    (H : GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : a∉lineEvents (realRootsThrough e C N) v k) :
    ChamberGeneric C N ((k+a • v).toAddMonoidHom.comp e) := by
  intro n hn hnN m hm hm0
  have hs:=realRoot_mem e C N n hnN m hm
  by_cases hv : v (e m)=0
  · have hk : k (e m)=0:=by
      change k (e m)+a*v (e m)=0 at hm0
      simpa only [hv,mul_zero,add_zero] using hm0
    apply H.avoid (e m) hs _ hk
    simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using
      realRoot_ne_zero C e L hdeg n hn m hm
  · exact ha ((mem_lineEvents_iff _ _ _ _).mpr ⟨e m,hs,hv,hm0⟩)

variable (u : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
lemma chamber_chart_trivial (F : CompletedPositive u Ω C) (N : ℕ)
    (h : M →+ ℝ) (H : ChamberGeneric C N h) :
    ∀n≤N,coeff n (chartZero u Ω C h F).val=coeff n 1 := by
  intro n hn
  cases n with
  | zero=>simpa only [coeff_zero_eq_constantCoeff,map_one] using
      (chartZero u Ω C h F).property.1
  | succ n=>
    rw [coeff_one,ite_eq_right (Nat.succ_ne_zero n)]
    apply Finsupp.ext
    intro m
    by_contra hm
    have hm' : coeff (n+1) (chartZero u Ω C h F).val m≠0:=hm
    exact H (n+1) (by omega) hn m
      (chart_root_of_ne u Ω C (chartZero u Ω C h F) (n+1) m hm')
      ((chart_three_support u Ω C h F).2.1 n m hm')

include hdeg in
lemma line_chart_trivial (F : CompletedPositive u Ω C) (N : ℕ)
    (v k : Module.Dual ℝ E) (H : GenericOffset (realRootsThrough e C N) 0 v k)
    (a : ℝ) (ha : a∉lineEvents (realRootsThrough e C N) v k) :
    ∀n≤N,coeff n (chartZero u Ω C ((k+a • v).toAddMonoidHom.comp e) F).val=coeff n 1 :=
  chamber_chart_trivial C u Ω F N _ (line_chamber_of_not_event C e L hdeg N v k H a ha)

omit [Module ℝ E] in
lemma realRootsThrough_mono {N K : ℕ} (h : N≤K) : realRootsThrough e C N⊆realRootsThrough e C K := by
  intro s hs
  obtain ⟨p,d,hd,hp,rfl⟩:=realRoot_exists C e N s hs
  exact realRoot_mem e C K d (hd.trans h) p hp

lemma lineEvents_mono {S T : Finset E} (h : S⊆T) (v k : Module.Dual ℝ E) :
    lineEvents S v k⊆lineEvents T v k := by
  intro a ha
  obtain ⟨s,hs,hv,hsa⟩:=(mem_lineEvents_iff _ _ _ _).mp ha
  exact (mem_lineEvents_iff _ _ _ _).mpr ⟨s,h hs,hv,hsa⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
