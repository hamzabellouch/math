import OAI.Combinatorics.SparsestCut.UniformReplication
import OAI.Combinatorics.SparsestCut.VertexCount

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceUniform
open scoped BigOperators
open SourceMetric SourceParameters
noncomputable section
lemma size_upper {d v : ℕ} (hd : 3≤d) (hv : v≤d^(4025*d)) :
    d^d+d^2*v+v≤d^(4030*d) := by
  have hd1 : 1≤d := by omega
  have hp : d^d≤d^(4025*d+2) := Nat.pow_le_pow_right hd1 (by omega)
  have hv' : v≤d^(4025*d+2) := hv.trans (Nat.pow_le_pow_right hd1 (by omega))
  have hprod : d^2*v≤d^(4025*d+2) := by
    calc
      _ ≤ d^2*d^(4025*d) := Nat.mul_le_mul_left _ hv
      _ = _ := by rw [←pow_add]; congr 1; omega
  calc
    _ ≤ 3*d^(4025*d+2) := by omega
    _ ≤ d*d^(4025*d+2) := Nat.mul_le_mul_right _ hd
    _ = d^(4025*d+3) := by rw [←pow_succ']
    _ ≤ _ := Nat.pow_le_pow_right hd1 (by omega)

lemma instance_exists {m : ℕ} (f : PivotFamily.PFamily (m+1))
    (hm : 3000 ≤ m+1) (hl : 1≤Real.log (m+1:ℕ)) (hH : SourceContraction.H≤(m+1:ℕ))
    (hD : 4*SourceWeighted.D≤(m+1:ℕ))
    (ha : C₀+1≤KernelApprox.cstar/6*(m+1:ℕ)) :
    ∃ (n : ℕ) (C : Capacity n), (m+1)^(m+1)≤n ∧ n≤(m+1)^(4030*(m+1)) ∧
      2≤n ∧ 1≤OPT C ∧ 0<glValue C ∧
      glValue C≤(SourceContraction.C+1)*SourceContraction.weight (m+1)/
        (KernelApprox.cstar/6*(m+1:ℕ)) := by
  classical
  let d := m+1
  have hd0 : 0<d := Nat.succ_pos m
  have hx0 : (0:ℝ)<d := by exact_mod_cast hd0
  have hd1 : 1≤d := by omega
  have hx : (1:ℝ)≤d := by exact_mod_cast hd1
  obtain ⟨Z,w,hw,hws,htri,hdiam,havg,hcon⟩ := SourceWeighted.weighted_instance f hm hl hH
  let M := d^d+d^2*Fintype.card (V f)
  have hM : 0<M := lt_of_lt_of_le (pow_pos hd0 _) (Nat.le_add_right _ _)
  let n := Replication.n M w
  let δ := fun i j : Fin n => ‖Z (Replication.rep M w i)-Z (Replication.rep M w j)‖^2
  let ε : ℝ := 4*(SourceWeighted.D*d)*(Fintype.card (V f):ℝ)/M
  have hε : ε≤1 := by
    apply (div_le_one (by exact_mod_cast hM)).mpr
    have hM' : (d:ℝ)^2*(Fintype.card (V f):ℝ)≤M := by
      exact_mod_cast (Nat.le_add_left (d^2*Fintype.card (V f)) (d^d))
    calc
      _ = (4*SourceWeighted.D)*(d:ℝ)*(Fintype.card (V f):ℝ) := by ring
      _ ≤ (d:ℝ)*(d:ℝ)*(Fintype.card (V f):ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hx0.le) (Nat.cast_nonneg _)
      _ = (d:ℝ)^2*(Fintype.card (V f):ℝ) := by ring
      _ ≤ _ := hM'
  have hsize := Replication.n_bounds M w hw hws
  have hlo : d^d≤n := (Nat.le_add_right _ _).trans hsize.1
  have hhi : n≤d^(4030*d) := hsize.2.trans (size_upper (by omega) (SourceCount.card_bound f (by omega)))
  have hn : 2≤n := by
    have hh : d≤d^d := by simpa using (Nat.pow_le_pow_right hd1 hd1 : d^1≤d^d)
    omega
  obtain ⟨hδ,hav,hco⟩ := UniformReplication.estimates M hM w hw hws Z htri
    (mul_nonneg SourceWeighted.D_pos.le hx0.le) hdiam havg hcon
  have ha0 : 0<KernelApprox.cstar/6*(d:ℝ) := mul_pos (div_pos KernelApprox.cstar_pos (by norm_num)) hx0
  have hb0 : 0<(SourceContraction.C+1)*SourceContraction.weight d := by
    have hc := SourceContraction.C_pos
    have hw' := SourceContraction.weight_ge_one hd1 hl
    positivity
  have hlow : KernelApprox.cstar/6*(d:ℝ)≤KernelApprox.cstar/3*(d:ℝ)-C₀*p d 8-ε := by
    have hp : C₀*p d 8≤C₀ := mul_le_of_le_one_right C₀_pos.le (p_one_le hx _)
    linarith only [ha,hp,hε]
  have hupp : SourceContraction.C*SourceContraction.weight d+ε≤
      (SourceContraction.C+1)*SourceContraction.weight d := by
    have hh := SourceContraction.weight_ge_one hd1 hl
    linarith only [hh,hε]
  obtain ⟨C,hopt,hgl,hbound⟩ := cut_cone_duality hn δ hδ ha0 hb0
    ((mul_le_mul_of_nonneg_left hlow (sq_nonneg (n:ℝ))).trans hav)
    (fun A hA F hF => (hco A F hF).trans (mul_le_mul_of_nonneg_left hupp (sq_nonneg (n:ℝ))))
  exact ⟨n,C,hlo,hhi,hn,hopt,hgl,hbound⟩
end
end UniformSparsestCut.SourceUniform

end

end OAI
