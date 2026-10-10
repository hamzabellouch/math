import OAI.NumberTheory.DirichletL.Descent.ActualChildStateSupport

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem actual_cell_path_lengths {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (Jo Jn : ℕ→ℕ) (source : (k : ℕ)→Finset (MarkedSecondSource ι (Jo k) (Jn k)))
    (cellIndex : ℕ→BlockIndex) (x : (k : ℕ)→MarkedSecondSource ι (Jo k) (Jn k))
    (F M r ell V A B t j b : ℕ→ℝ) (Z eta cutoff : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hsmall : eta≤cutoff/16) (n : ℕ)
    (hsource : ∀k<n,
      ActualSecondSourceConditions p (source k) ∧
      (∀y∈source k,y.second.frequency≠0) ∧ x k∈cell p (source k) (cellIndex k) ∧
      F k=r k+3*ell k+V k ∧
      0≤A k ∧ 0≤t k ∧ 0≤ell k ∧ 0≤V k ∧ cutoff≤ell k+V k ∧
      1≤b k ∧ b k≤Z^(6*eta) ∧
      (∀y∈source k,primeProductNorm p y.second.sourceCommon*primeProductNorm p y.second.overlap≤
        b k*Z^(r k-A k-B k-t k)) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.leftExponent)‖^2≤Z^(ell k+eta) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.rightExponent)‖^2≤Z^(ell k+eta) ∧
      Z^(j k-eta)≤‖eisEmbedding (jLabel p (x k).cube.support
        (fun i=>(x k).cube.leftExponent i+(x k).cube.rightExponent i)
        (x k).cube.leftBit (x k).cube.rightBit)‖^2)
    (hF : ∀k<n,F (k+1)=actualCellTotalExponent Z (Z^(r k-A k-B k-t k)) (B k) (j k) eta (cellIndex k))
    (hM : ∀k<n,M (k+1)=childM (M k) (ell k) (A k) (t k)
      (secondCellExponent Z (cellIndex k) 0) (secondCellExponent Z (cellIndex k) 1) (V k) (j k) eta) :
    F n≤F 0+15*(n:ℝ)*eta ∧ M n+3*(n:ℝ)*cutoff/2≤M 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n<n+1 := Nat.lt_succ_self n
    obtain ⟨hs,hk,hx,hparent,hA,ht,hell,hV,hterm,hb,hthreshold,hgeom,h1,h2,hj⟩ := hsource n hn
    have hi := ih (fun k hk=>hsource k (Nat.lt_trans hk hn))
      (fun k hk=>hF k (Nat.lt_trans hk hn)) (fun k hk=>hM k (Nat.lt_trans hk hn))
    have hf := actual_cell_child_total_upper p hp (source n) hs hk (cellIndex n) (x n) hx
      Z (r n) (ell n) (V n) (A n) (B n) (t n) (j n) eta (b n) hZ hA ht hell hV heta hbin
      hb hthreshold hgeom h1 h2 hj
    have hm := actual_cell_row_decrease p hp (source n) hs hk (cellIndex n) (x n) hx
      Z (M n) (ell n) (A n) (t n) (V n) (j n) eta cutoff hZ hA ht heta hbin hterm hsmall h1 h2 hj
    rw [←hF n hn,←hparent] at hf
    rw [←hM n hn] at hm
    push_cast
    constructor <;> linarith [hi.1,hi.2]

theorem actual_cell_depth_caps (F M N V F0 M0 eta : ℝ) (n depth : ℕ)
    (hn : n≤depth) (heta : 0≤eta) (hF : F≤F0+15*(n:ℝ)*eta)
    (hM : M≤M0) (hN : 0≤N) (hV : 0≤V) (hsum : F=N+V) :
    N≤F0+15*(depth:ℝ)*eta ∧ V≤F0+15*(depth:ℝ)*eta ∧ M≤M0 := by
  have hn' : (n:ℝ)≤depth := by exact_mod_cast hn
  have he := mul_le_mul_of_nonneg_right hn' heta
  constructor
  · linarith
  constructor
  · linarith
  · exact hM

theorem actual_cell_depth_bound (M M0 cutoff : ℝ) (n : ℕ) (hcutoff : 0<cutoff)
    (hM : 0≤M) (hpath : M+3*(n:ℝ)*cutoff/2≤M0) :
    (n:ℝ)≤2*M0/(3*cutoff) := by
  apply (le_div_iff₀ (by positivity : 0<3*cutoff)).mpr
  nlinarith

end SevenEighths.InverseMoment
end

end OAI
