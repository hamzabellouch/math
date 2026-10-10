import OAI.Geometry.Convex.GeneralMahler.Middle.Cells

namespace OAI
/-! Arithmetic verification of compact region. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Grid Jet Profile Segment SE Cert Cert.IV
def everyF (p:Ft→Bool):Bool:= [Ft.K,Ft.C,Ft.Q,Ft.M,Ft.J,Ft.V].all p
lemma chk_every (p:Ft→Bool)(h:everyF p=true)(t:Ft):p t=true:=
  List.all_eq_true.mp h t (by cases t <;> decide)
variable (B:PrefixC)
def initC:=everyF (fun t=>SubB 0 (B 0 t))
def ctStep (n:Nat):=everyF (fun t=>SubB (B n t+aStep n t) (B (n+1) t))
lemma cWorks (h:initC B=true) (he:By (ctStep B) 0 720):Works B:=
  ⟨chk_every _ h,fun n hn=>chk_every _ (he n (by omega) hn)⟩

-- Blocks left i≤280 step8, right j≤720 step8
def tile (b:Bool)(i j:Nat):Bool:=quadRun B b 3 (8*i) (8*j)
def GoodS (b:Bool):Prop:=∀ i,i<35→By (tile B b i) 0 90
def Good := GoodS B true∧ GoodS B false

lemma colG {b:Bool}(h:NG)(g:Works B)(he:GoodS B b){x y:ℝ}
    (ha:0 ≤ x)(hb:x≤nd 280)(hc:x≤y)(hd:y≤nd 720)(hh:32/100≤ y-signF b x) :
    Fval (signF b x) y <0 := by
  have hi (n:ℕ) (x:ℝ) (h₀:0 ≤ x)(h₁:x≤nd (8*n))(hp:0<n):
      ∃ i,i<n∧ nd (8*i) ≤ x ∧ x ≤ nd (8*i+8) := by
    induction n with
    | zero => omega
    | succ n ih=>
      by_cases h:x≤ nd (8*n)
      · by_cases h':0<n
        · obtain ⟨i,hi,hh⟩:=ih h h'; exact ⟨i,by omega,hh⟩
        have hj:n=0:= by omega
        subst n
        exact ⟨0,by omega, by simpa only [Nat.mul_zero,nd0] using h₀, h₁⟩
      exact ⟨n,by omega,le_of_lt (lt_of_not_ge h),by rw [show 8*n+8=8*(n+1) by omega];exact h₁⟩
  obtain ⟨i,ht,hx,hv⟩:=hi 35 x ha hb (by decide)
  obtain ⟨j,hu,hj,hj'⟩:=hi 90 y (ha.trans hc) hd (by decide)
  apply quadR B b h g 3 _ _ (by norm_num; omega) (by norm_num; omega)
    (he i ht j (by omega) hu) x y (show InRegion b (8*i) (8*j) (2^3) _ _ from
      ⟨hx,hv,hj,hj',hc,hh⟩)
lemma has_middle (b:PrefixC)(h:NG)(he:Works b)(hh:Good b)(x y:ℝ)
    (hx:|x|≤14/10)(hy:y≤36/10)(hz:|x|≤y)(hp:32/100≤ y-x):
    symR (xs x,xs y)<0:=by
  rw [← poly_E h]
  have hl: |x| ≤ nd 280:=by norm_num [nd] at *; exact hx
  have hr:y≤ nd 720:=by norm_num [nd] at *; exact hy
  rcases le_total 0 x with H|H
  · rw [abs_of_nonneg H] at *
    exact colG b h he hh.2 H hl hz hr hp
  rw [abs_of_nonpos H] at *
  have hb : signF true (-x)=x:= neg_neg _
  rw [← hb]; apply colG b h he hh.1 (neg_nonneg.mpr H) hl hz hr _
  rw [hb];exact hp
end GeneralMahler.SCal.Mid

end OAI
