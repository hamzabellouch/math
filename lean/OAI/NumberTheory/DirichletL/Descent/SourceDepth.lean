import OAI.NumberTheory.DirichletL.Descent.SecondSharpPuncture

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)

include hp in

theorem actual_second_childF_upper {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor⊆x.second.sourceCommon)
    (Z F ell A t g theta V j delta eta : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (hell : 0≤ell) (hV : 0≤V) (hdelta : delta≤6*eta)
    (hG : primeProductNorm p x.second.sourceCommon≤Z^(g+eta))
    (hD : Z^(theta-eta)≤primeProductNorm p x.second.divisor)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childF F ell A t g theta V j delta≤F+11*eta :=
  childF_upper hA ht hell hV
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD)
    (actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ) hdelta

include hp in

theorem actual_source_path_lengths
    (Jo Jn : ℕ→ℕ) (x : (k : ℕ)→MarkedSecondSource ι (Jo k) (Jn k))
    (F M ell A t g theta V j delta : ℕ→ℝ) (Z eta d : ℝ) (hZ : 1<Z)
    (n : ℕ) (heta : eta≤d/16)
    (hsource : ∀ k<n,
      (x k).second.divisor⊆(x k).second.sourceCommon ∧
      0≤A k ∧ 0≤t k ∧ 0≤ell k ∧ 0≤V k ∧ delta k≤6*eta ∧ d≤ell k+V k ∧
      primeProductNorm p (x k).second.sourceCommon≤Z^(g k+eta) ∧
      Z^(theta k-eta)≤primeProductNorm p (x k).second.divisor ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.leftExponent)‖^2≤Z^(ell k+eta) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.rightExponent)‖^2≤Z^(ell k+eta) ∧
      Z^(j k-eta)≤‖eisEmbedding (jLabel p (x k).cube.support
        (fun i=>(x k).cube.leftExponent i+(x k).cube.rightExponent i)
        (x k).cube.leftBit (x k).cube.rightBit)‖^2)
    (hF : ∀ k<n,F (k+1)=childF (F k) (ell k) (A k) (t k) (g k) (theta k) (V k) (j k) (delta k))
    (hM : ∀ k<n,M (k+1)=childM (M k) (ell k) (A k) (t k) (g k) (theta k) (V k) (j k) eta) :
    F n≤F 0+11*(n:ℝ)*eta ∧ M n+3*(n:ℝ)*d/2≤M 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n<n+1 := Nat.lt_succ_self n
    obtain ⟨he,ha,ht,hl,hv,hd,hterm,hg,hdiv,h1,h2,hj⟩ := hsource n hlt
    have hi := ih (fun k hk=>hsource k (Nat.lt_trans hk hlt))
      (fun k hk=>hF k (Nat.lt_trans hk hlt)) (fun k hk=>hM k (Nat.lt_trans hk hlt))
    have hf := actual_second_childF_upper p hp (x n) he Z (F n) (ell n) (A n) (t n)
      (g n) (theta n) (V n) (j n) (delta n) eta hZ ha ht hl hv hd hg hdiv h1 h2 hj
    have hm := actual_second_row_decrease p hp (x n) he Z (M n) (ell n) (A n) (t n)
      (g n) (theta n) (V n) (j n) eta d hZ ha ht hterm heta hg hdiv h1 h2 hj
    rw [←hF n hlt] at hf
    rw [←hM n hlt] at hm
    push_cast
    constructor <;> linarith [hi.1,hi.2]

theorem source_depth_caps (F M N V F0 M0 eta : ℝ) (n D : ℕ) (hn : n≤D)
    (heta : 0≤eta) (hF : F≤F0+11*(n:ℝ)*eta) (_hM : 0≤M) (hMm : M≤M0)
    (hN : 0≤N) (hV : 0≤V) (hsum : F=N+V) :
    N≤F0+11*(D:ℝ)*eta ∧ V≤F0+11*(D:ℝ)*eta ∧ M≤M0 := by
  have hn' : (n:ℝ)≤D := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hn' heta
  constructor
  · linarith
  constructor
  · linarith
  · exact hMm

end
end SevenEighths.InverseMoment

end OAI
