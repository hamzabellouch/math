import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.NearCutGeometry

namespace OAI

section
namespace ElementaryPositivity.AffineCut
noncomputable section
variable {G:Type*} [Group G]
def oldGauge (g:G) (side:Bool) : G := if side then g⁻¹ else 1
def oldFactor (g:G) (u v t:ℝ) : G := if u+t*v=0 then if v<0 then g else g⁻¹ else 1
lemma oldFactor_local (g:G) (u v t:ℝ) (hne:u≠0 ∨ v≠0) (x:G) :
    oldFactor g u v t*(oldGauge g (beforeSide u v t)*x)=oldGauge g (afterSide u v t)*x := by
  by_cases hz:u+t*v=0
  · have hv:v≠0:=by rintro rfl; simp_all
    rw [oldFactor,ite_eq_left hz,(sides_at_zero u v t hz).1,(sides_at_zero u v t hz).2]
    rcases lt_or_gt_of_ne hv with hn|hp
    · simp [oldGauge,hn,show ¬0<v by linarith,←mul_assoc]
    · simp [oldGauge,hp,show ¬v<0 by linarith]
  · rw [oldFactor,ite_eq_right hz,(sides_eq_of_ne u v t hz).1,(sides_eq_of_ne u v t hz).2,one_mul]
lemma oldFactor_telescope (g:G) (u v lo hi:ℝ) (hlohi:lo<hi) (hne:u≠0 ∨ v≠0)
    (hlo:u+lo*v≠0) (hhi:u+hi*v≠0) (T:Finset ℝ) (hmem:∀t∈T,lo<t ∧ t<hi)
    (hcut:∀t,lo<t → t<hi → u+t*v=0 → t∈T) :
    ((T.sort (· ≥ ·)).map (oldFactor g u v)).prod*oldGauge g (decide (0<u+lo*v))=
      oldGauge g (decide (0<u+hi*v)) := by
  classical
  have H:=telescope_sort u v hne (fun _ (x:G)=>x) (fun t x=>oldFactor g u v t*x)
    (fun side x=>oldGauge g side*x) T lo hi hlohi hmem hcut
    (fun t _ x=>oldFactor_local g u v t hne x) 1
  have hid:(T.sort (· ≥ ·)).foldr (fun _ (x:G)=>x) 1=1:=by
    generalize T.sort (· ≥ ·)=l
    induction l <;> simp_all
  have hmul:∀l:List ℝ,∀x:G,l.foldr (fun t x=>oldFactor g u v t*x) x=
      (l.map (oldFactor g u v)).prod*x:=by
    intro l x
    induction l with
    | nil=>simp
    | cons a l ih=>simp only [List.foldr_cons,List.map_cons,List.prod_cons,ih,mul_assoc]
  rw [(sides_eq_of_ne u v lo hlo).2,(sides_eq_of_ne u v hi hhi).1,hid,mul_one,mul_one,hmul] at H
  exact H
end
end ElementaryPositivity.AffineCut

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k:Module.Dual ℝ E) (H:∀N,GenericOffset (realRootsThrough e C N) 0 v k)

include he hdeg H in
omit [FiniteDimensional ℝ E] in
lemma nearCut_letter (a:ℝ) (hh:NearCut Ω C pc e (k+a • v)) :
    comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)=
    AffineCut.oldFactor (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc))
      (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a := by
  classical
  by_cases hp:(k+a • v) (e (simpleRoot C pc))=0
  · have ha:∃N,a∈lineEvents (realRootsThrough e C N) v k:=⟨1,line_cut_event C pc e L hdeg v k H a hp⟩
    unfold actualLineLetter
    simp only [dite_eq_left ha,dite_eq_left hp]
    have hp':k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0:=hp
    rw [AffineCut.oldFactor,ite_eq_left hp']
    by_cases hv:v (e (simpleRoot C pc))<0 <;> simp only [hv,decide_true,decide_false,comparisonOld,↓reduceIte]
  · have hp':k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))≠0:=hp
    rw [AffineCut.oldFactor,ite_eq_right hp']
    by_cases ha:∃N,a∈lineEvents (realRootsThrough e C N) v k
    · obtain ⟨r,d,hd,hr,hv,hg,HE⟩:=actualLineLetter_old Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a ha
      have HC:=nearCut_noncut_wall Ω C coord hcoord pc e he S hS hcomp L hdeg (k+a • v) hh
        r d hd hr hg (decide (0<(k+a • v) (e (simpleRoot C pc))))
        (cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp)
      have HU:completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
          (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C))=1:=by
        apply Units.ext
        apply Subtype.ext
        exact HC
      rw [HE,HU]
      split_ifs <;> simp
    · simp only [actualLineLetter,dite_eq_right ha,comparisonOld]

include he hdeg H in
omit [FiniteDimensional ℝ E] in
lemma nearCut_line_word (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k)
    (hh:∀t,lo≤t → t≤hi → NearCut Ω C pc e (k+t • v)) (N:ℕ) (hN:1≤N) :
    comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)*
      AffineCut.oldGauge (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc)) (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      AffineCut.oldGauge (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc)) (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  classical
  unfold comparisonWordOld actualLineWord
  rw [List.map_map]
  have HH:=AffineCut.oldFactor_telescope
    (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc))
    (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) lo hi hlohi
    (Or.inl (line_cut_offset_ne C pc e L hdeg v k H))
    (fun hz=>hlo (line_cut_event C pc e L hdeg v k H lo hz))
    (fun hz=>hhi (line_cut_event C pc e L hdeg v k H hi hz))
    (intervalLineEvents C e v k lo hi N) (fun a ha=>(Finset.mem_filter.mp ha).2)
    (fun a hla hah hz=>Finset.mem_filter.mpr ⟨lineEvents_mono (realRootsThrough_mono C e hN) v k
      (line_cut_event C pc e L hdeg v k H a hz),hla,hah⟩)
  rw [show (intervalEventList C e v k lo hi N).map
      ((comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)) ∘
      actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H)=_ from
    List.map_congr_left (fun a ha=>nearCut_letter Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
      (hh a (Finset.mem_filter.mp ((Finset.mem_sort _).mp ha)).2.1.le
        (Finset.mem_filter.mp ((Finset.mem_sort _).mp ha)).2.2.le))]
  exact HH
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

include he hdeg in
omit [FiniteDimensional ℝ E] in
lemma nearCut_path_word {a b:Module.Dual ℝ E} (p:GenericLinePath C e a b)
    (hh:p.InRegion C e {h | NearCut Ω C pc e h}) (N:ℕ) (hN:1≤N) :
    comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N)*
      AffineCut.oldGauge (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc)) (decide (0<a (e (simpleRoot C pc))))=
      AffineCut.oldGauge (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc)) (decide (0<b (e (simpleRoot C pc)))) := by
  induction p with
  | nil=>simp only [actualPathWord,comparisonWordOld,List.map_nil,List.prod_nil,one_mul]
  | append s p ih=>
    rw [actualPathWord,comparisonWordOld_append,mul_assoc,ih hh.2]
    exact nearCut_line_word Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi s.ordered (s.start_regular 1) (s.finish_regular 1) hh.1 N hN

include he hdeg S hS hcomp in
lemma nearCut_chart_ratio (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (hap:a (e (simpleRoot C pc))<0) (hbp:0<b (e (simpleRoot C pc))) :
    covectorNegativeUnit Ω C coord hcoord pc e b*(covectorNegativeUnit Ω C coord hcoord pc e a)⁻¹=
      (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc))⁻¹ := by
  obtain ⟨p,hp⟩:=nearCut_path Ω C pc e hC HA HB ha hb
  have HW:∀N,1≤N → comparisonWordOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
      (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualPathWord Ω C coord hcoord pc e he S hS hcomp L hdeg p N)=
      (oldPureUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc))⁻¹:=by
    intro N hN
    have H:=nearCut_path_word Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p hp N hN
    simpa only [AffineCut.oldGauge,decide_eq_false (not_lt.mpr hap.le),Bool.false_eq_true,ite_false,
      decide_eq_true hbp,ite_true,mul_one] using H
  apply Units.ext
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  have HH:=actualPath_old_transport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg p (max 1 n)
  have Hx:=(oldCoefficientsEqual_equivalence Ω coord pc (max 1 n)).refl
    (covectorNegativeUnit Ω C coord hcoord pc e a)⁻¹
  have H:=oldCoefficientsEqual_mul Ω coord pc (max 1 n) _ _ _ _ HH Hx
  rw [mul_assoc,mul_inv_cancel,mul_one,HW _ (le_max_left _ _)] at H
  exact (H n (le_max_right _ _)).symm
end
end ElementaryPositivity.RationalFiber

end

end OAI
