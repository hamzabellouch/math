import OAI.Dynamics.StandardMap.BridgeDirichlet

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma phi_remainder_lipschitz (k x u v R : ℝ) (hk : 0 ≤ k) (hu : |u| ≤ R) (hv : |v| ≤ R) :
    |(phi k (x+u)-phi k x-potential k x*u)-
      (phi k (x+v)-phi k x-potential k x*v)| ≤
      (2*Real.pi*growthBase k)*R*|u-v| := by
  let f := fun z => phi k (x+z)-phi k x-potential k x*z
  have hd' (z : ℝ) : HasDerivAt f (potential k (x+z)-potential k x) z := by
    have hh:=((hasDerivAt_phi k (x+z)).comp z ((hasDerivAt_const z x).add (hasDerivAt_id z))).sub_const (phi k x)
    have hh':=hh.sub ((hasDerivAt_id z).const_mul (potential k x))
    convert! hh' using 1; simp
  have hC : 0 ≤ 2*Real.pi*growthBase k := by have := growthBase_ge_four k hk; positivity
  have hf:=Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := fun z => potential k (x+z)-potential k x)
    (s := uIcc v u) (C := (2*Real.pi*growthBase k)*R)
    (fun z _ => (hd' z).hasDerivWithinAt)
    (by
      intro z hz
      rw [Real.norm_eq_abs]
      have hzR : |z| ≤ R := by
        have hmin : -R ≤ min v u := le_min (abs_le.mp hv).1 (abs_le.mp hu).1
        have hmax : max v u ≤ R := max_le (abs_le.mp hv).2 (abs_le.mp hu).2
        exact abs_le.mpr ⟨hmin.trans hz.1,hz.2.trans hmax⟩
      calc
        _ ≤ (2*Real.pi*growthBase k)*|x+z-x| := potential_lipschitz k x (x+z) hk
        _ ≤ _ := by simpa only [add_sub_cancel_left] using mul_le_mul_of_nonneg_left hzR hC)
    (convex_uIcc v u) left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs,f] using hf

lemma finite_weighted_dirichlet {ι : Type*} [Fintype ι]
    (w U : ι → ℝ) (G : ι → ι → ℝ) (F : ι → ℝ → ℝ) (L : ι → ℝ) (r R : ℝ)
    (hw : ∀ i, 0 < w i) (hR : 0 ≤ R) (hL : ∀ i, 0 ≤ L i)
    (hzero : ∀ i, F i 0=0)
    (hLip : ∀ i x y, |x| ≤ R/w i → |y| ≤ R/w i → |F i x-F i y| ≤ L i*|x-y|)
    (hlin : ∀ i, |w i*U i*r| ≤ R/2)
    (hrow : ∀ i, ∑ j, |w i*G i j| *L j/w j ≤ 1/2) :
    ∃ ξ : ι → ℝ, (∀ i, |ξ i| ≤ R/w i) ∧
      ∀ i, ξ i=U i*r+∑ j, G i j*F j (ξ j) := by
  classical
  let T : (ι → ℝ) → (ι → ℝ) := fun X i => w i*U i*r+∑ j, w i*G i j*F j (X j/w j)
  have hcoord (X : ι → ℝ) (hX : ‖X‖ ≤ R) (i : ι) : |X i/w i| ≤ R/w i := by
    rw [abs_div,abs_of_pos (hw i)]
    exact div_le_div_of_nonneg_right (((norm_le_pi_norm X i)).trans hX) (hw i).le
  have hdiff (X Y : ι → ℝ) (hX : ‖X‖ ≤ R) (hY : ‖Y‖ ≤ R) : ‖T X-T Y‖ ≤ (1/2)*‖X-Y‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hc (j : ι) : |X j/w j-Y j/w j| ≤ ‖X-Y‖/w j := by
      rw [← sub_div,abs_div,abs_of_pos (hw j)]
      exact div_le_div_of_nonneg_right (norm_le_pi_norm (X-Y) j) (hw j).le
    calc
      ‖(T X-T Y) i‖ = |∑ j, w i*G i j*(F j (X j/w j)-F j (Y j/w j))| := by
        simp only [Pi.sub_apply,T,Real.norm_eq_abs,add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ j, |w i*G i j| *|F j (X j/w j)-F j (Y j/w j)| := by
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => w i*G i j*(F j (X j/w j)-F j (Y j/w j))) Finset.univ
      _ ≤ ∑ j, |w i*G i j| *(L j*(‖X-Y‖/w j)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left ((hLip j _ _ (hcoord X hX j) (hcoord Y hY j)).trans
          (mul_le_mul_of_nonneg_left (hc j) (hL j))) (abs_nonneg _)
      _ = (∑ j, |w i*G i j| *L j/w j)*‖X-Y‖ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)
  have hT0 : ‖T 0‖ ≤ R/2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    simpa only [T,Pi.zero_apply,zero_div,hzero,mul_zero,Finset.sum_const_zero,add_zero,Real.norm_eq_abs] using hlin i
  have hmaps : MapsTo T (closedBall (0:(ι→ℝ)) R) (closedBall 0 R) := by
    intro X hX
    rw [mem_closedBall_zero_iff] at hX ⊢
    have hd:=hdiff X 0 hX (by simpa using hR)
    have htri:=norm_le_norm_sub_add (T X) (T 0)
    simp only [sub_zero] at hd
    nlinarith
  have hcont : ContractingWith (1/2:NNReal) (hmaps.restrict T (closedBall 0 R) (closedBall 0 R)) := by
    constructor
    · norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro X Y
      have hh:=hdiff X Y (mem_closedBall_zero_iff.mp X.property) (mem_closedBall_zero_iff.mp Y.property)
      change ‖T (X : ι → ℝ)-T (Y : ι → ℝ)‖ ≤ (↑(1/2:NNReal):ℝ)*‖(X : ι → ℝ)-(Y : ι → ℝ)‖
      simpa only [NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using hh
  obtain ⟨X,hX,hfix,_,_⟩:=hcont.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
    (x := (0:ι→ℝ)) (by simpa using hR) (edist_ne_top _ _)
  have hXnorm : ‖X‖ ≤ R := by simpa using hX
  refine ⟨fun i => X i/w i,fun i => hcoord X hXnorm i,?_⟩
  intro i
  have hh:=congrFun hfix i
  dsimp [T] at hh
  apply (div_eq_iff (hw i).ne').mpr
  rw [← hh]
  rw [add_mul,Finset.sum_mul]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    ring
end StandardMapEntropy

end OAI
