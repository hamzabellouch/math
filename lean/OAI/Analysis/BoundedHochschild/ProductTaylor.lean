import Mathlib

namespace OAI

/-! Noncommutative product expansions and linear and quadratic error terms. -/

noncomputable section



 

 

 

namespace HochschildPatching
namespace ProductTaylor
variable {R : Type*} [Ring R]
def oldProduct (l : List (R × R)) : R := (l.map Prod.fst).prod
def totalProduct (l : List (R × R)) : R := (l.map (fun ab => ab.1+ab.2)).prod
@[simp] lemma old_nil : oldProduct ([] : List (R × R))=1 := rfl
@[simp] lemma total_nil : totalProduct ([] : List (R × R))=1 := rfl
@[simp] lemma old_cons (ab : R × R) (l : List (R × R)) : oldProduct (ab::l)=ab.1*oldProduct l := rfl
@[simp] lemma total_cons (ab : R × R) (l : List (R × R)) : totalProduct (ab::l)=(ab.1+ab.2)*totalProduct l := rfl
lemma old_append (l r : List (R × R)) : oldProduct (l++r)=oldProduct l*oldProduct r := by
  simp only [oldProduct,List.map_append,List.prod_append]
lemma total_append (l r : List (R × R)) : totalProduct (l++r)=totalProduct l*totalProduct r := by
  simp only [totalProduct,List.map_append,List.prod_append]

def differenceTerms : List (R × R) → List R
  | [] => []
  | ab::l => ab.2*totalProduct l :: (differenceTerms l).map (fun x => ab.1*x)
def linearTerms : List (R × R) → List R
  | [] => []
  | ab::l => ab.2*oldProduct l :: (linearTerms l).map (fun x => ab.1*x)
def quadraticTerms : List (R × R) → List R
  | [] => []
  | ab::l => (differenceTerms l).map (fun x => ab.2*x) ++ (quadraticTerms l).map (fun x => ab.1*x)

lemma sum_map_mul_left (a : R) (l : List R) : (l.map (fun x => a*x)).sum=a*l.sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons,List.sum_cons,ih,mul_add]

lemma total_eq_old_add_difference (l : List (R × R)) : totalProduct l=oldProduct l+(differenceTerms l).sum := by
  induction l with
  | nil => simp [differenceTerms]
  | cons ab l ih =>
    simp only [total_cons,old_cons,differenceTerms,List.sum_cons,sum_map_mul_left]
    rw [ih]
    noncomm_ring
lemma total_eq_old_add_linear_add_quadratic (l : List (R × R)) :
    totalProduct l=oldProduct l+(linearTerms l).sum+(quadraticTerms l).sum := by
  induction l with
  | nil => simp [linearTerms,quadraticTerms]
  | cons ab l ih =>
    simp only [total_cons,old_cons,linearTerms,quadraticTerms,List.sum_cons,List.sum_append,sum_map_mul_left]
    have hd := total_eq_old_add_difference l
    have ht : (differenceTerms l).sum=(linearTerms l).sum+(quadraticTerms l).sum := by
      rw [ih] at hd
      rw [add_assoc] at hd
      exact (add_left_cancel hd).symm
    rw [ht,ih]
    noncomm_ring

lemma mem_differenceTerms {l : List (R × R)} {x : R} (hx : x ∈ differenceTerms l) :
    ∃ pre ab post, l=pre++ab::post ∧ x=oldProduct pre*ab.2*totalProduct post := by
  induction l generalizing x with
  | nil => simp only [differenceTerms,List.not_mem_nil] at hx
  | cons ab l ih =>
    simp only [differenceTerms,List.mem_cons,List.mem_map] at hx
    rcases hx with rfl|⟨y,hy,rfl⟩
    · exact ⟨[],ab,l,rfl,by simp⟩
    · obtain ⟨pre,cd,post,hr,rfl⟩ := ih hy
      exact ⟨ab::pre,cd,post,by simp only [List.cons_append,hr],by simp only [old_cons,mul_assoc]⟩
lemma mem_linearTerms {l : List (R × R)} {x : R} (hx : x ∈ linearTerms l) :
    ∃ pre ab post, l=pre++ab::post ∧ x=oldProduct pre*ab.2*oldProduct post := by
  induction l generalizing x with
  | nil => simp only [linearTerms,List.not_mem_nil] at hx
  | cons ab l ih =>
    simp only [linearTerms,List.mem_cons,List.mem_map] at hx
    rcases hx with rfl|⟨y,hy,rfl⟩
    · exact ⟨[],ab,l,rfl,by simp⟩
    · obtain ⟨pre,cd,post,hr,rfl⟩ := ih hy
      exact ⟨ab::pre,cd,post,by simp only [List.cons_append,hr],by simp only [old_cons,mul_assoc]⟩
lemma mem_quadraticTerms {l : List (R × R)} {x : R} (hx : x ∈ quadraticTerms l) :
    ∃ pre ab middle cd post, l=pre++ab::(middle++cd::post) ∧
      x=oldProduct pre*ab.2*oldProduct middle*cd.2*totalProduct post := by
  induction l generalizing x with
  | nil => simp only [quadraticTerms,List.not_mem_nil] at hx
  | cons ab l ih =>
    simp only [quadraticTerms,List.mem_append,List.mem_map] at hx
    rcases hx with ⟨y,hy,rfl⟩|⟨y,hy,rfl⟩
    · obtain ⟨middle,cd,post,hr,rfl⟩ := mem_differenceTerms hy
      exact ⟨[],ab,middle,cd,post,by simp only [List.nil_append,hr],by simp only [old_nil,one_mul,mul_assoc]⟩
    · obtain ⟨pre,cd,middle,ef,post,hr,rfl⟩ := ih hy
      exact ⟨ab::pre,cd,middle,ef,post,by simp only [List.cons_append,hr],by simp only [old_cons,mul_assoc]⟩

lemma differenceTerms_length (l : List (R × R)) : (differenceTerms l).length=l.length := by
  induction l with
  | nil => rfl
  | cons ab l ih => simp only [differenceTerms,List.length_cons,List.length_map,ih]
lemma linearTerms_length (l : List (R × R)) : (linearTerms l).length=l.length := by
  induction l with
  | nil => rfl
  | cons ab l ih => simp only [linearTerms,List.length_cons,List.length_map,ih]
lemma quadraticTerms_length_le (l : List (R × R)) : (quadraticTerms l).length ≤ l.length^2 := by
  induction l with
  | nil => simp [quadraticTerms]
  | cons ab l ih =>
    simp only [quadraticTerms,List.length_append,List.length_map,differenceTerms_length,List.length_cons]
    nlinarith
end ProductTaylor
end HochschildPatching
end

end OAI
