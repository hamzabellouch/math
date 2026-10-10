import OAI.Analysis.LienardCycles.RealAnalysis

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.EndpointAlgebra

lemma X_reparam {M N L : ℝ → ℝ} {x m n l w a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => X (M t) (N t) (L t)) (X1 m n l w*a) x := by
  have hm' : M x ≠ 0 := by rwa [hMv]
  have hn' : N x ≠ 0 := by rwa [hNv]
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := ((hL.div hM hm').sub ((hasDerivAt_const x (1:ℝ)).div hN hn')).div
    (hL.const_add 1) hl'
  convert! hd using 1
  simp only [Pi.div_apply,Pi.sub_apply,hMv,hNv,hLv]
  dsimp [X1,Z1]
  field_simp
  ring

lemma Z_reparam {M N L : ℝ → ℝ} {x m n l w a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => Z (M t) (N t) (L t)) (Z1 m n l w*a) x := by
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := ((hL.mul hM).sub hN).div (hL.const_add 1) hl'
  convert! hd using 1
  simp only [Pi.sub_apply,Pi.mul_apply,hMv,hNv,hLv]
  dsimp [Z1]
  field_simp
  ring

lemma N0_reparam {M N L : ℝ → ℝ} {x m n l w a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hm : m ≠ 0) (hn : n ≠ 0) :
    HasDerivAt (fun t => N0 (M t) (N t) (L t)) (N1 m n l w*a) x := by
  have hm' : M x ≠ 0 := by rwa [hMv]
  have hn' : N x ≠ 0 := by rwa [hNv]
  have hd := (hL.div (hM.pow 2) (pow_ne_zero _ hm')).add
    ((hasDerivAt_const x (1:ℝ)).div (hN.pow 2) (pow_ne_zero _ hn'))
  convert! hd using 1
  simp only [Pi.pow_apply,hMv,hNv,hLv]
  dsimp [N1]
  field_simp
  ring

lemma gamma_reparam {M N L : ℝ → ℝ} {x m n l w a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => gamma (M t) (N t) (L t)) (gamma1 m n l w*a) x := by
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := (N0_reparam hM hN hL hMv hNv hLv hm hn).div (hL.const_add 1) hl'
  convert! hd using 1
  simp only [hMv,hNv,hLv]
  dsimp [gamma1]
  field_simp

lemma Z1_reparam {M N L W : ℝ → ℝ} {x m n l w s a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hW : HasDerivAt W ((s+(1/2)*w^2)*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hWv : W x=w) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => Z1 (M t) (N t) (L t) (W t)) (Z2 m n l w s*a) x := by
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := (((hL.mul hW).mul (hM.add hN)).div
    ((hL.const_add 1).pow 2) (pow_ne_zero _ hl'))
  convert! hd using 1
  simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,hMv,hNv,hLv,hWv]
  dsimp [Z2]
  field_simp
  ring

lemma X1_reparam {M N L W : ℝ → ℝ} {x m n l w s a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hW : HasDerivAt W ((s+(1/2)*w^2)*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hWv : W x=w)
    (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => X1 (M t) (N t) (L t) (W t)) (X2 m n l w s*a) x := by
  have hm' : M x ≠ 0 := by rwa [hMv]
  have hn' : N x ≠ 0 := by rwa [hNv]
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hB := ((hasDerivAt_const x (1:ℝ)).div (hN.pow 2) (pow_ne_zero _ hn')).sub
    ((hasDerivAt_const x (1:ℝ)).div (hM.pow 2) (pow_ne_zero _ hm'))
  have hd := ((hL.mul hB).div (hL.const_add 1) hl').add
    ((Z1_reparam hM hN hL hW hMv hNv hLv hWv hl).div (hM.mul hN) (mul_ne_zero hm' hn'))
  convert! hd using 1
  simp only [Pi.div_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,hMv,hNv,hLv,hWv]
  dsimp [X2]
  field_simp
  ring

lemma N1_reparam {M N L W : ℝ → ℝ} {x m n l w s a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hW : HasDerivAt W ((s+(1/2)*w^2)*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hWv : W x=w) (hm : m ≠ 0) (hn : n ≠ 0) :
    HasDerivAt (fun t => N1 (M t) (N t) (L t) (W t)) (N2 m n l w s*a) x := by
  have hm' : M x ≠ 0 := by rwa [hMv]
  have hn' : N x ≠ 0 := by rwa [hNv]
  have hd := (((hL.mul hW).div (hM.pow 2) (pow_ne_zero _ hm')).sub
    ((hL.const_mul 2).div (hM.pow 3) (pow_ne_zero _ hm'))).sub
      ((hL.const_mul 2).div (hN.pow 3) (pow_ne_zero _ hn'))
  convert! hd using 1
  simp only [Pi.mul_apply,Pi.pow_apply,hMv,hNv,hLv,hWv]
  dsimp [N2]
  field_simp
  ring

lemma gamma1_reparam {M N L W : ℝ → ℝ} {x m n l w s a : ℝ}
    (hM : HasDerivAt M a x) (hN : HasDerivAt N (l*a) x) (hL : HasDerivAt L (l*w*a) x)
    (hW : HasDerivAt W ((s+(1/2)*w^2)*a) x)
    (hMv : M x=m) (hNv : N x=n) (hLv : L x=l) (hWv : W x=w)
    (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    HasDerivAt (fun t => gamma1 (M t) (N t) (L t) (W t)) (gamma2 m n l w s*a) x := by
  have hl' : 1+L x ≠ 0 := by rwa [hLv]
  have hd := ((N1_reparam hM hN hL hW hMv hNv hLv hWv hm hn).div (hL.const_add 1) hl').sub
    ((((N0_reparam hM hN hL hMv hNv hLv hm hn).mul hL).mul hW).div
      ((hL.const_add 1).pow 2) (pow_ne_zero _ hl'))
  convert! hd using 1
  simp only [Pi.mul_apply,Pi.pow_apply,hMv,hNv,hLv,hWv]
  dsimp [gamma2]
  field_simp
  ring
end QuinticLienard.EndpointAlgebra

end OAI
