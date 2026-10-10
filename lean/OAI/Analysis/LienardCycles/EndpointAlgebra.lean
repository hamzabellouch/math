import OAI.Analysis.LienardCycles.ModelAlgebra

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.EndpointAlgebra
open ModelAlgebra
noncomputable def X (m n l : ℝ) : ℝ := (l/m-1/n)/(1+l)
noncomputable def Z (m n l : ℝ) : ℝ := (l*m-n)/(1+l)
noncomputable def gamma (m n l : ℝ) : ℝ := (l/m^2+1/n^2)/(1+l)
noncomputable def Z1 (m n l w : ℝ) : ℝ := l*w*(m+n)/(1+l)^2
noncomputable def Z2 (m n l w s : ℝ) : ℝ :=
  l*(s+3/2*w^2)*(m+n)/(1+l)^2+l*w/(1+l)-2*l^2*w^2*(m+n)/(1+l)^3
noncomputable def X1 (m n l w : ℝ) : ℝ := l*(1/n^2-1/m^2)/(1+l)+Z1 m n l w/(m*n)
noncomputable def X2 (m n l w s : ℝ) : ℝ :=
  l*w*(1/n^2-1/m^2)/(1+l)^2+l*(2/m^3-2*l/n^3)/(1+l)+
    Z2 m n l w s/(m*n)-Z1 m n l w*(n+m*l)/(m^2*n^2)
noncomputable def N0 (m n l : ℝ) : ℝ := l/m^2+1/n^2
noncomputable def N1 (m n l w : ℝ) : ℝ := l*w/m^2-2*l/m^3-2*l/n^3
noncomputable def N2 (m n l w s : ℝ) : ℝ :=
  l*(s+3/2*w^2)/m^2-4*l*w/m^3+6*l/m^4-2*l*w/n^3+6*l^2/n^4
noncomputable def gamma1 (m n l w : ℝ) : ℝ := N1 m n l w/(1+l)-N0 m n l*l*w/(1+l)^2
noncomputable def gamma2 (m n l w s : ℝ) : ℝ :=
  N2 m n l w s/(1+l)-2*N1 m n l w*l*w/(1+l)^2-
    N0 m n l*l*(s+3/2*w^2)/(1+l)^2+2*N0 m n l*(l*w)^2/(1+l)^3

lemma determinant {m n l w s : ℝ} (hm : m ≠ 0) (hn : n ≠ 0) (hl : 1+l ≠ 0) :
    X1 m n l w*Z2 m n l w s-Z1 m n l w*X2 m n l w s =
      l^2*(m+n)^2/(m^2*n^2*(1+l)^3)*dStar m n l w s := by
  dsimp [X1,X2,Z1,Z2,dStar]
  field_simp
  ring

lemma gamma_identity {m n l w s : ℝ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hl : 1+l ≠ 0) (hmn : m+n ≠ 0) :
    (m-n)*(gamma2 m n l w s*X1 m n l w-gamma1 m n l w*X2 m n l w s)-
      l*(m+n)^2/((1+l)*m^2*n^2)*(wStar m n l-w)*X1 m n l w =
      l^2*(m+n)^2*(m^2+n^2)/((1+l)^3*m^4*n^4)*dStar m n l w s := by
  dsimp [gamma2,gamma1,N0,N1,N2,X1,X2,Z1,Z2,wStar,dStar]
  field_simp
  ring

lemma gamma_factor {m n l w s : ℝ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hl : 1+l ≠ 0) (hmn : m+n ≠ 0) (hneq : m ≠ n)
    (hx : X1 m n l w ≠ 0) (hd : dStar m n l w s=0) :
    gamma2 m n l w s-X2 m n l w s/X1 m n l w*gamma1 m n l w =
      l*(m+n)^2/((1+l)*m^2*n^2)*(wStar m n l-w)/(m-n) := by
  have hh := gamma_identity (w := w) (s := s) hm hn hl hmn
  rw [hd,mul_zero] at hh
  have hdiff : m-n ≠ 0 := sub_ne_zero.mpr hneq
  apply (eq_div_iff hdiff).mpr
  field_simp [hx] at *
  nlinarith only [hh]

end QuinticLienard.EndpointAlgebra

end OAI
