import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutatedAnchors
import OAI.Combinatorics.Chromatic.GradedAlgebra.HomogeneousElementaryExpressions
import OAI.Combinatorics.Chromatic.QuantumTorus.CovectorPrescriptions
import OAI.Combinatorics.Chromatic.Walls.GenericAffineProbes

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (pc:I) (e:M →+ E)

omit [FiniteDimensional ℝ E] in
lemma nearCut_convex {a b:Module.Dual ℝ E} (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b)
    (t:ℝ) (ht:0≤t) (ht':t≤1) : NearCut Ω C pc e ((1-t) • a+t • b) := by
  by_cases ht1:t=1
  · subst t
    simpa using hb
  have htt:0<1-t:=sub_pos.mpr (lt_of_le_of_ne ht' ht1)
  constructor
  · rw [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.smul_apply,smul_eq_mul,smul_eq_mul]
    have A:=abs_lt.mp ha.1
    have B:=abs_lt.mp hb.1
    apply abs_lt.mpr
    constructor
    · nlinarith [mul_pos htt (sub_pos.mpr A.1),mul_nonneg ht (sub_nonneg.mpr B.1.le)]
    · nlinarith [mul_pos htt (sub_pos.mpr A.2),mul_nonneg ht (sub_nonneg.mpr B.2.le)]
  · intro i hi
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
    nlinarith [mul_pos htt (sub_pos.mpr (ha.2 i hi)),
      mul_nonneg ht (sub_nonneg.mpr (hb.2 i hi).le)]

def nearCutProbes : Finset (ℝ×E) := by
  classical
  exact (Finset.univ.erase pc).image (fun i=>(1,e (simpleRoot C i))) ∪
    {(-1/((mutationSize Ω C pc:ℝ)+1),e (simpleRoot C pc)),
     (1/((mutationSize Ω C pc:ℝ)+1),e (simpleRoot C pc))}

omit [FiniteDimensional ℝ E] in
lemma nearCut_of_probes (J k h:Module.Dual ℝ E) (hJ:∀i,J (e (simpleRoot C i))=1)
    (hk:NearCut Ω C pc e k)
    (hh:∀x∈nearCutProbes Ω C pc e,
      (0<(k+x.1 • J) x.2 → 0<(h+x.1 • J) x.2) ∧
      ((k+x.1 • J) x.2<0 → (h+x.1 • J) x.2<0)) : NearCut Ω C pc e h := by
  classical
  have Hp: (1/((mutationSize Ω C pc:ℝ)+1),e (simpleRoot C pc))∈nearCutProbes Ω C pc e:=by
    simp [nearCutProbes]
  have Hn: (-1/((mutationSize Ω C pc:ℝ)+1),e (simpleRoot C pc))∈nearCutProbes Ω C pc e:=by
    simp [nearCutProbes]
  have Hk:=abs_lt.mp hk.1
  constructor
  · apply abs_lt.mpr
    have A:0<(h+(1/((mutationSize Ω C pc:ℝ)+1)) • J) (e (simpleRoot C pc)):=by
      apply (hh _ Hp).1
      simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hJ,mul_one]
      linarith
    have B:(h+(-1/((mutationSize Ω C pc:ℝ)+1)) • J) (e (simpleRoot C pc))<0:=by
      apply (hh _ Hn).2
      simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hJ,mul_one,neg_div]
      linarith
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,hJ,mul_one,neg_div] at A B
    constructor <;> linarith
  · intro i hi
    have Hi:(1,e (simpleRoot C i))∈nearCutProbes Ω C pc e:=by
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩,rfl⟩)
    have A:(h+(1:ℝ) • J) (e (simpleRoot C i))<0:=by
      apply (hh _ Hi).2
      simp only [one_smul,LinearMap.add_apply,hJ]
      linarith [hk.2 i hi]
    simp only [one_smul,LinearMap.add_apply,hJ] at A
    linarith

lemma nearCut_path (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i)))
    {a b:Module.Dual ℝ E} (HA:RegularCovector C e a) (HB:RegularCovector C e b)
    (ha:NearCut Ω C pc e a) (hb:NearCut Ω C pc e b) :
    ∃p:GenericLinePath C e a b,p.InRegion C e {h | NearCut Ω C pc e h} := by
  obtain ⟨J,hJ⟩:=real_covector_prescribe C e hC (fun _=>1)
  apply generic_region_path_via_probes C e a b a (nearCutProbes Ω C pc e) J HA HB
  intro h hh
  have Hh:=nearCut_of_probes Ω C pc e J a h hJ ha hh
  exact ⟨fun t ht ht'=>nearCut_convex Ω C pc e ha Hh t ht ht',
    fun t ht ht'=>nearCut_convex Ω C pc e Hh hb t ht ht'⟩

lemma nearCut_regular_point (hC:LinearIndependent ℝ (fun i=>e (simpleRoot C i))) (pos:Bool) :
    ∃h:Module.Dual ℝ E,RegularCovector C e h ∧ NearCut Ω C pc e h ∧
      cutSide pos (h.toAddMonoidHom.comp e) (simpleRoot C pc) := by
  classical
  let ε:ℝ:=1/((mutationSize Ω C pc:ℝ)+1)
  have hep:0<ε:=by dsimp [ε]; positivity
  obtain ⟨J,hJ⟩:=real_covector_prescribe C e hC (fun _=>1)
  obtain ⟨k,hk⟩:=real_covector_prescribe C e hC (fun i=>if i=pc then if pos then ε/2 else -ε/2 else -2)
  have hkn:NearCut Ω C pc e k:=by
    constructor
    · rw [hk]; simp only [ite_true]
      cases pos <;> simp only [Bool.false_eq_true,ite_false,ite_true,abs_div,abs_of_pos hep,
        abs_neg,abs_of_pos (show (0:ℝ)<2 by norm_num)]
      all_goals change _<ε; linarith
    · intro i hi; rw [hk,ite_eq_right hi]; norm_num
  let P:=insert ((0:ℝ),e (simpleRoot C pc)) (nearCutProbes Ω C pc e)
  obtain ⟨h,Ha,Hb,HP⟩:=generic_for_two_directions_with_probes (realRootsThrough e C) 0 0 k P J
  have Hreg:RegularCovector C e h:=by
    intro N s hs hn
    exact (Ha N).avoid s hs (by simpa only [Submodule.span_zero_singleton,Submodule.mem_bot] using hn)
  refine ⟨h,Hreg,nearCut_of_probes Ω C pc e J k h hJ hkn
    (fun x hx=>HP x (Finset.mem_insert_of_mem hx)),?_⟩
  have Hcut:=HP ((0:ℝ),e (simpleRoot C pc)) (Finset.mem_insert_self _ _)
  simp only [zero_smul,add_zero] at Hcut
  cases pos
  · change h (e (simpleRoot C pc))<0
    apply Hcut.2
    rw [hk]; simp only [ite_true,Bool.false_eq_true,ite_false]
    linarith
  · change 0<h (e (simpleRoot C pc))
    apply Hcut.1
    rw [hk]; simp only [ite_true]
    linarith

omit [FiniteDimensional ℝ E] in
lemma nearCut_old_negative {h:Module.Dual ℝ E} (hh:NearCut Ω C pc e h)
    (hp:h (e (simpleRoot C pc))<0) : ∀n,0<n → ∀m,HasRootDegree C n m → h (e m)<0 := by
  have H:∀i,0<(-h) (e (simpleRoot C i)):=by
    intro i
    simp only [LinearMap.neg_apply,neg_pos]
    by_cases hi:i=pc
    · simpa only [hi] using hp
    · linarith [hh.2 i hi]
  intro n hn m hm
  simpa only [LinearMap.neg_apply,neg_pos] using covector_root_pos C e (-h) H hn hm

omit [FiniteDimensional ℝ E] in
lemma nearCut_new_negative {h:Module.Dual ℝ E} (hh:NearCut Ω C pc e h)
    (hp:0<h (e (simpleRoot C pc))) :
    ∀n,0<n → ∀m,HasRootDegree (mutatedRoots Ω C pc) n m → h (e m)<0 := by
  have H:∀i,0<(-h) (e (simpleRoot (mutatedRoots Ω C pc) i)):=by
    intro i
    simp only [LinearMap.neg_apply,neg_pos]
    by_cases hi:i=pc
    · subst i
      rw [mutatedRoot_p,map_neg,map_neg]
      linarith
    · rw [mutatedRoot_off Ω C pc i hi,map_add,map_zsmul,map_add,map_zsmul,zsmul_eq_mul]
      have hc:0≤(max 0 (-mutationPairing Ω C pc i):ℝ):=by positivity
      have hb:(max 0 (-mutationPairing Ω C pc i):ℝ)≤(mutationSize Ω C pc:ℝ):=by
        have H:=mutationSize_bound Ω C pc i hi
        have HH:max 0 (-mutationPairing Ω C pc i)≤(mutationSize Ω C pc:ℤ):=
          max_le (by positivity) ((neg_le_abs _).trans H)
        exact_mod_cast HH
      have heps:= (abs_lt.mp hh.1).2
      have hB:0≤(mutationSize Ω C pc:ℝ):=by positivity
      have hm:(mutationSize Ω C pc:ℝ)*h (e (simpleRoot C pc))<1:=by
        have Hmul:((mutationSize Ω C pc:ℝ)+1)*h (e (simpleRoot C pc))<1:=by
          have Hmul: h (e (simpleRoot C pc))*((mutationSize Ω C pc:ℝ)+1)<1:=
            (lt_div_iff₀ (by positivity)).mp heps
          nlinarith
        nlinarith
      simp only [Int.cast_max,Int.cast_zero,Int.cast_neg]
      nlinarith [hh.2 i hi,mul_le_mul_of_nonneg_right hb hp.le]
  intro n hn m hm
  simpa only [LinearMap.neg_apply,neg_pos] using
    covector_root_pos (mutatedRoots Ω C pc) e (-h) H hn hm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
